/-
MazurTorsion.lean — own work for the Fermat project (not vendored from the
FLT project).

Decomposition of `FreyPackage.mazur` (irreducibility of the mod-`p` Galois
representation on the `p`-torsion of the Frey curve) into two nodes,
following Serre's argument (Duke Math. J. 54 (1987), §4.1).

LABEL AUDIT (bookkeeping, 2026-07-25): the two nodes below, and
`card_torsionBy_dvd_of_charP` further down, no longer carry a `sorry` in
their own bodies — Lean reports no `declaration uses 'sorry'` warning for
any of them, so they are NOT dispatchable leaves and their old "(sorry
node)" labels were manufacturing phantom work.  (This file does still
have 26 genuinely sorried declarations; those keep their labels.  Note
these three may still be transitively open through the leaves they
consume — "no direct sorry" is the claim here, not full cleanliness.)

* `FreyPackage.exists_torsion_embedding_of_not_isIrreducible` (no direct sorry):
  **Serre's reducible-case analysis.** If the mod-`p` representation of the
  Frey curve `E` is not irreducible, then there is a Galois-stable line in
  `E[p]` (the `p`-torsion is `2`-dimensional over `𝔽_p`, so a proper nonzero
  invariant submodule is a line), i.e. a rational subgroup `C ⊆ E` of order
  `p`, giving an extension `0 → χ₁ → E[p] → χ₂ → 0` of characters with
  `χ₁ χ₂ = ω̄` (mod-`p` cyclotomic, by the Weil pairing). The Frey curve is
  semistable, so both characters are unramified away from `p` (unipotent
  inertia at multiplicative primes, triviality at good primes), and at `p`
  one of them is unramified (the supersingular case is excluded because
  inertia at `p` then acts irreducibly, contradicting reducibility). An
  everywhere-unramified character of `Gal(ℚ̄/ℚ)` is trivial (Minkowski: `ℚ`
  has no unramified extension). If `χ₁ = 1` then `E` has a rational point
  of order `p`; if `χ₂ = 1` then the quotient curve `E' = E/C` (a `ℚ`-rational
  quotient by a rational subgroup, Vélu) has one, namely the image of `E[p]`.
  Whichever curve carries the point of order `p` also carries full rational
  `2`-torsion: `E` visibly (`y² = x(x − aᵖ)(x + bᵖ)` has `(0,0)`, `(aᵖ,0)`,
  `(−bᵖ,0)`), and `E/C` because the quotient isogeny has odd degree `p`
  (so is injective on `E[2]`) and is defined over `ℚ`. Since `p` is odd,
  `(ℤ/2)² × ℤ/p ≅ ℤ/2 × ℤ/2p`, so SOME elliptic curve over `ℚ` has a
  subgroup of rational points isomorphic to `ℤ/2 × ℤ/2p`. The statement
  folds the quotient-curve construction (not yet available in mathlib) into
  an existential over Weierstrass models; a later layer must construct
  quotients by finite rational subgroups and split this node accordingly.

* `WeierstrassCurve.mazur_classification` (no direct sorry): **Mazur's torsion
  theorem** (Mazur, 1977/1978), stated faithfully: the torsion subgroup of
  the rational points of an elliptic curve over `ℚ` is isomorphic to one of
  the fifteen groups `ℤ/n` for `n ∈ {1, …, 10, 12}` or `ℤ/2 × ℤ/2m` for
  `m ∈ {1, 2, 3, 4}`.

* `WeierstrassCurve.mazur_torsion_bound` (PROVEN from the classification):
  **Mazur's torsion theorem, weak form.** No elliptic curve over `ℚ` has a
  subgroup of rational points isomorphic to `ℤ/2 × ℤ/2p` for a prime
  `p ≥ 5`. Derivation: the image of an injective homomorphism
  `ℤ/2 × ℤ/2p →+ E(ℚ)` consists of torsion points (every element of the
  finite source has finite additive order), so the homomorphism corestricts
  to an injection into the torsion subgroup; by the classification the
  torsion subgroup is finite of order at most `16`, while the source has
  order `4p ≥ 20`.

Given the two nodes, `FreyPackage.mazur` is immediate: if the representation
were reducible, the first node produces a curve whose rational points contain
`ℤ/2 × ℤ/2p`, which the second node forbids.
-/
module

public import Fermat.FLT.FreyCurve.Basic
public import Fermat.FLT.EllipticCurve.Torsion
-- `natDegree_Φ`, `leadingCoeff_Φ`, `natDegree_ΨSq_le` and the Bézout
-- relation `isCoprime_Φ_ΨSq`: the division-polynomial inputs of the
-- `p`-divisibility of the kernel of reduction
-- (`exists_localKernelDivision_of_good_reduction`). Both modules are
-- already in the transitive cone through `TorsionCard`, but only via
-- PRIVATE imports there, which are not re-exported — so they must be
-- imported publicly here.
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import Fermat.FLT.EllipticCurve.PhiPsiCoprime
-- Vélu's construction of the quotient of an elliptic curve by a finite
-- Galois-stable subgroup of odd order (`exists_velu_quotient_isogeny`), which
-- discharges `exists_quotient_isogeny_of_odd_prime_card` below.
public import Fermat.FLT.EllipticCurve.Velu
-- `cyclotomicCharacterModL` and the stable-line extraction, used in the
-- character bookkeeping of the Serre §4.1 dichotomy.
public import Fermat.FLT.GaloisRepresentation.Chebotarev
-- `det_galoisRep_eq_cyclotomic` (the DERIVED determinant node), the
-- `χ₁χ₂ = ω̄` input of the dichotomy derivation.
public import Fermat.FLT.EllipticCurve.WeilPairing
-- `FreyCurve.torsion_isUnramified` (unramifiedness outside `{2, p}`),
-- consumed by the derivation of the semistability leaf.
public import Fermat.FLT.GaloisRepresentation.HardlyRamified.FreyConditions
-- `localInertiaGroup` and the restriction `Γ ℚ_q → Γ ℚ`, used to state
-- the Minkowski node.
public import Fermat.FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
-- `Nat.Prime.toHeightOneSpectrumRingOfIntegersRat`, the place of `ℚ`
-- attached to a prime number.
public import Fermat.FLT.Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
-- the reduction-of-POINTS theory (`WeierstrassCurve.IsReductionAlong`, `redHom`),
-- used in SIGNATURE position by the local reduction leaves below, hence `public`
public import Fermat.FLT.KnownIn1980s.EllipticCurves.PointReduction
-- Minkowski's discriminant theorem (`exists_not_isUnramifiedAt_int_of_isGalois`)
-- and the going-up prime lifting, used in the Minkowski assembly proof.
import Mathlib.NumberTheory.NumberField.ExistsRamified
import Mathlib.RingTheory.Ideal.GoingUp
-- The local inertia-fixed-field node (`e(M/ℚ_q) = 1` for finite
-- subextensions of `ℚ_qᵃˡᵍ` fixed by the local inertia), consumed by
-- the transport proof of the Minkowski surjectivity theorem below.
import Fermat.FLT.Deformations.RepresentationTheory.LocalInertiaFixedField
-- `adicCompletion.maximalIdeal_eq_span_uniformizer`, used to identify
-- the maximal ideal of `ℤ_q` with the span of `q`.
import Fermat.FLT.DedekindDomain.AdicValuation
-- The structure theorem for finite abelian groups
-- (`AddCommGroup.equiv_directSum_zmod_of_finite`) and the `ZMod` Chinese
-- remainder theorem (`ZMod.prodEquivPi`), used in the PROVEN rank-`≤ 2`
-- decomposition backing Mazur's classification.
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Data.ZMod.QuotientRing
-- The unramified quadratic twist to split multiplicative reduction and
-- its Galois-equivariant point equivalence, consumed by the PROVEN
-- local torsion quotient of the nonsplit multiplicative case
-- (`exists_localTorsionQuotient_of_nonsplit`).
import Fermat.FLT.KnownIn1980s.EllipticCurves.QuadraticTwists.SplitMultiplicativeReduction
-- Fermat's little theorem (`ZMod.pow_card_sub_one_eq_one`), the cyclic
-- structure of a group of prime order (`isAddCyclic_of_prime_card`), and
-- Lagrange for the quotient by the eigenline
-- (`AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup`): the three
-- inputs of the Borel exponent bound `borel_bound_iterate_eq_self`.
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coset.Card
-- `not_fermat_42` and the classification of primitive Pythagorean triples: the two
-- classical inputs of the `X_1(16)` descent in `MazurSixteen.not_sextic_square`.
import Mathlib.NumberTheory.FLT.Four
-- `fermatLastTheoremThree` (and `fermatLastTheoremFor_iff_rat`, re-exported
-- through it): the Mordell–Weil half of the `X_0(27)` node below.  `X_0(27)`
-- IS the Fermat cubic — `y² + y = x³ − 7` is `Y² = X³ − 432` is `x³ + y³ = z³`
-- — so the determination of its rational points is exactly Fermat's Last
-- Theorem for exponent `3`.  See `MazurLevel27.rational_point_x0TwentySeven`.
import Mathlib.NumberTheory.FLT.Three
-- `TorsionCharP.exists_zsmul_eq_of_charP`: cyclicity of the geometric
-- `p`-torsion in characteristic `p`, the inseparability input of
-- `exists_zsmul_eq_of_mem_torsionBy_of_charP` below.
import Fermat.FLT.EllipticCurve.TorsionCharP
-- The Gaussian-integer infinite descent on `e² = X⁴ − 11X²Y² − Y⁴`: the
-- arithmetic input of the `X_1(2,10)` node
-- (`MazurTwoTen.quartic_no_solution`).
public import Fermat.FLT.FreyCurve.QuarticDescent

@[expose] public section

open WeierstrassCurve WeierstrassCurve.Affine

/-!
### Decomposition of Mazur's classification (2026-07-22)

`mazur_classification` is decomposed; after the third pass
(2026-07-22, night) the remaining SORRY leaves are exactly the
genuinely modular-curve-theoretic inputs:

* `mazur_point_order` (DERIVED 2026-07-23 from the two leaves below
  and the PROVEN divisor-closure reduction
  `MazurPointOrder.mem_of_no_forbidden_divisor`): Mazur's uniform
  bound — the order of a rational torsion point lies in
  `{1, …, 10, 12}` (Mazur 1977, Thm 8).
* `no_prime_torsion_ge_eleven` (PROVEN 2026-07-25 as the eight-way
  case split over the primes that survive the `X_0` cut): no rational
  point of prime order `ℓ ≥ 11` (Mazur 1977, Thm 7). Every `ℓ` outside
  `{11, 13, 17, 19, 37, 43, 67, 163}` is discharged outright by the
  `X_0` node `mem_cyclicIsogenyDegrees` — a point of order `ℓ`
  generates a rational cyclic `ℓ`-isogeny, and those eight are the
  only primes `≥ 11` in Kenku's list. The eight per-level statements
  `no_torsion_order_11`, …, `no_torsion_order_163` are PROVEN in turn
  from the PROVEN Tate normal form `exists_tateNormalForm` (new here,
  no mathlib counterpart), which puts a curve with a point of order
  `≥ 4` into the shape `y² + (1 − c)xy − by = x³ − bx²` with the point
  at the origin. So the content that remains sits in the eight
  Tate-coordinate nodes `tateNormalForm_origin_order_ne_11`, …,
  `_163` — plane models of `X_1(ℓ)` in the `(b, c)`-coordinates — all
  IRREDUCIBLE at this mathlib pin: all eight `ℓ` ARE rational isogeny
  degrees, so the `X_0` shortcut provably stops there and only
  `X_1(ℓ)` excludes the point. See the section notes before them for
  the witnesses, the genera and the missing-machinery list.
* `no_composite_torsion_order` (PROVEN 2026-07-25 as the eleven-way
  case split over its `Finset` hypothesis): no rational point of
  order `n ∈ {14, 15, 16, 18, 20, 21, 24, 25, 27, 35, 49}` — the
  minimal composite orders outside the list. The content sits in the
  eleven per-level nodes `no_torsion_order_14`, …,
  `no_torsion_order_49`, one classical theorem each (Kubert, Ligozat,
  Kenku; subsumed in Mazur 1977, Thm 8). Nine of the eleven are now
  PROVEN (2026-07-25), along two complementary routes determined by the
  single criterion in the section note below — whether the level is
  absent from Kenku's list of rational cyclic isogeny degrees:
  - *absent, so the `X_0` route applies*: `20, 24, 35, 49`, each PROVEN
    from the one `X_0` node `WeierstrassCurve.mem_cyclicIsogenyDegrees`
    through the PROVEN bridge `mem_cyclicIsogenyDegrees_of_addOrderOf`;
  - *present, so only `X_1` excludes the point*: `14, 15, 16, 18`,
    each PROVEN from a level-structure leaf
    (`not_order_two_and_order_seven_point`,
    `not_order_three_and_order_five_point`,
    `not_halved_order_eight_point`,
    `not_order_two_and_order_nine_point`) stating the same
    modular-curve content in the literature's own shape.
  - *present, but sharpened through `X_0(27)` anyway*: `27`, PROVEN
    from `j_of_stable_cyclic_subgroup_order_27` (the `j`-invariant of
    the unique non-cuspidal rational point of `X_0(27)`) and
    `no_torsion_order_27_of_j`, which was Olson's CM torsion theorem and
    is now itself PROVEN (2026-07-25) over the genus-`0` curve
    `X_1(9)`: a point of order `27` gives one of order `9`, which puts
    the curve on the Kubert line, and `j = −12288000` there is a
    degree-`36` equation in the Kubert parameter with no rational root.
    `j_of_stable_cyclic_subgroup_order_27` is itself PROVEN (2026-07-26)
    over two shallower moduli leaves, `exists_x0Nine_hauptmodul` (the
    genus-`0` curve `X_0(9)` with its explicit degree-`12` `j`-map) and
    `exists_x0TwentySeven_point` (the degree-`3` degeneracy map
    `X_0(27) → X_0(9)` in the model `27a1 : y² + y = x³ − 7`); its
    Mordell–Weil half is gone entirely, being
    `MazurLevel27.rational_point_x0TwentySeven`, PROVEN from mathlib's
    `fermatLastTheoremThree` because `X_0(27)` IS the Fermat cubic.
    `exists_x0TwentySeven_point` is in turn PROVEN (2026-07-26) over
    `exists_x0TwentySeven_moduliPoint`, the remaining arithmetic — that
    the `j₉`-fibre over `−12288000` has the one rational point `t = −3` —
    being `MazurLevel27.x0Nine_fibre_over_CM`; and
    `exists_x0TwentySeven_moduliPoint` is itself PROVEN (2026-07-26) over
    the single LEVEL-`3` leaf `exists_x0Three_chainParameters`, by the
    `3`-isogeny chain, everything above level `3` having been reduced to
    proven arithmetic over `ℚ`.
  The two levels `21, 25` are in Kenku's list and have no sharpening
  yet, so they are the only bare sorry nodes left among the eleven.
* `torsion_finite_rat` (DERIVED from `mazur_point_order`): the
  rational torsion subgroup is finite — every rational torsion point
  is killed by `2520 = lcm(1, …, 10, 12)`, and the geometric
  `2520`-torsion is finite.
* `not_full_odd_prime_torsion_rat` (PROVEN, from the DERIVED
  determinant node): no rational `(ℤ/ℓ)²` for an odd prime `ℓ` — a
  rational full level-`ℓ` structure trivializes the mod-`ℓ`
  representation, hence its determinant, the mod-`ℓ` cyclotomic
  character, forcing `μ_ℓ ⊆ ℚ`.
* `not_full_four_torsion_rat` (PROVEN 2026-07-22): no rational
  `(ℤ/4)²`, by the elementary square-product argument on the
  `2`-torsion abscissae (`cubic_vieta` + `halving_square` +
  `exists_halving_coords`, all PROVEN pure algebra).
* `not_full_torsion_rat` (DERIVED from the two preceding nodes): for
  `n ≥ 3` the full `n`-torsion is never rational.
* `not_two_ten_torsion`, `not_two_twelve_torsion` (DERIVED 2026-07-23
  from the two leaves below by primary decomposition of the level
  structure): no rational `ℤ/2 × ℤ/10` or `ℤ/2 × ℤ/12` (the modular
  curves `X_1(2,10)` and `X_1(2,12)` have genus ≥ 1 and no
  non-cuspidal rational points; part of the fifteen-groups list of
  Mazur 1977).
* `not_two_torsion_and_five_point` (PROVEN 2026-07-25 modulo ONE
  arithmetic leaf — the earlier "IRREDUCIBLE" verdict is SUPERSEDED):
  full rational `2`-torsion plus a point of order `5`. The order-`5`
  point gives a Tate parameter `c ≠ 0` with `u¹²Δ_E = c⁵(c² − 11c − 1)`
  (`MazurTwoTen.exists_tate_disc_of_order_five`, PROVEN 2026-07-25), and full
  `2`-torsion makes `Δ_E` a square
  (`MazurTwoTen.exists_disc_sq_of_full_two_torsion`, PROVEN); together
  they force a rational point with `c ≠ 0` on the conductor-`20`,
  rank-`0` curve `v² = c³ − 11c² − c`, excluded by
  `MazurTwoTen.no_rational_solution` (PROVEN) down to
  `MazurTwoTen.quartic_no_solution` (`e² = X⁴ − 11X²Y² − Y⁴` has no
  coprime nonzero solution), itself PROVEN 2026-07-25 by the Gaussian
  infinite descent of `Fermat/FLT/FreyCurve/QuarticDescent.lean`. No
  modular curve is constructed anywhere.
* `not_two_four_torsion_and_three_point` (PROVEN 2026-07-25 modulo one
  quartic): a rational `ℤ/2 × ℤ/4` plus a point of order `3`
  (`X_1(2,12)`; Kenku, Mazur 1977 Thm 8). Its own IRREDUCIBLE audit was
  refuted the same day: halving one `2`-torsion point makes BOTH
  differences of abscissae squares, not just their product
  (`MazurTwoTwelve.halving_squares`), and the order-`3` point is an
  inflection, so the level structure cuts down by elementary algebra to
  the plane quartic `MazurTwoTwelve.quartic_only_trivial`
  (`v² = (j²−1)(j²+3)` has no rational point with `v ≠ 0` — the
  conductor-`24` rank-`0` curve `24a`), itself PROVEN 2026-07-26 by the
  elementary descent in `MazurTwoTwelve.Quartic`.
* `not_two_cube_torsion` (PROVEN): no rational `(ℤ/2)³` — the geometric
  `2`-torsion has only `2² = 4` points.
* `AddCommGroup.exists_rank_le_two_decomposition` (PROVEN — pure
  finite-abelian-group bookkeeping over the structure theorem and the
  `ZMod` Chinese remainder theorem).
* `mazur_group_casework` (PROVEN): given the `ℤ/d × ℤ/n` shape, the
  order bound, and the two exclusions, the group is one of the fifteen.
-/

/-!
#### The eleven critical composite levels, one node each

`no_composite_torsion_order` is PROVEN below as the eleven-way case
split over its `Finset` hypothesis; the mathematical content sits in the
eleven per-level nodes `no_torsion_order_14`, …, `no_torsion_order_49`.
Each of the eleven is one classical theorem — "the modular curve
`X_1(n)` has no non-cuspidal rational point" for that single `n`.
EIGHT of the eleven are PROVEN (2026-07-25): `20, 24, 35, 49` from the
single `X_0` node `mem_cyclicIsogenyDegrees` stated just below, and
`14, 15, 16, 18` from the four level-structure leaves, exactly as the
criterion at the end of this note dictates. The three that remain —
`21, 25, 27` — are IRREDUCIBLE literature citations at this mathlib pin
(audit 2026-07-25): there is no modular-curve theory available here,
the `X_0` shortcut provably does not apply at those levels, and the two
elementary routes that could conceivably shortcut a level both fail
uniformly.

* *Divisor reduction fails by design.* Every proper divisor of each of
  the eleven levels lies in Mazur's allowed set `{1, …, 10, 12}`, so no
  level follows from another level, nor from
  `no_prime_torsion_ge_eleven`; that minimality is exactly what
  `MazurPointOrder.mem_of_no_forbidden_divisor` consumes.
* *Reduction at a good prime plus the Hasse bound fails.* Rational
  torsion injects into `Ẽ(𝔽_p)` for every odd prime `p` of good
  reduction (and the odd part does at `p = 2`), so a rational point of
  order `n` forces `n ≤ p + 1 + 2√p` at every such `p`. For `n = 14`
  that only excludes good reduction at `2, 3, 5` — a lower bound on the
  conductor, never a contradiction, since curves of every such
  conductor exist.

A formal proof of any one node needs `X_1(n)` as an arithmetic curve
over `ℚ` together with a determination of its rational points: a
rank-`0` Mordell–Weil computation for the genus-one levels `14, 15`,
and Chabauty/Kenku-style arguments (or the Eisenstein-ideal descent)
for the higher-genus levels. Genera, computed from the standard formula
`g(X_1(N)) = 1 + (N²/24)∏_{p ∣ N}(1 − p⁻²) − ¼ Σ_{d ∣ N} φ(d)φ(N/d)`:
`14 ↦ 1`, `15 ↦ 1`, `16 ↦ 2`, `18 ↦ 2`, `20 ↦ 3`, `21 ↦ 5`, `24 ↦ 5`,
`25 ↦ 12`, `27 ↦ 13`, `35 ↦ 25`, `49 ↦ 69`.

THE `X_0` / ISOGENY SHORTCUT — THE CRITERION, STATED ONCE (2026-07-25,
reconciling two independent same-day audits). A rational point of order
`n` generates a rational, hence Galois-stable, cyclic subgroup of order
`n`, i.e. a rational cyclic `n`-isogeny. So the shortcut "`X_0(n)`
already has no non-cuspidal rational point" is available at a level `n`
IF AND ONLY IF `n` is ABSENT from Kenku's list
`{1, …, 19, 21, 25, 27, 37, 43, 67, 163}` of rational cyclic isogeny
degrees (Mazur 1978 for the prime degrees, Kenku 1979–1982 for the
composite ones). That single criterion decides every level:

* ABSENT from the list, shortcut AVAILABLE: `20, 24, 35, 49`. All four
  are PROVEN below from the one `X_0` node
  `WeierstrassCurve.mem_cyclicIsogenyDegrees` through the PROVEN bridge
  `mem_cyclicIsogenyDegrees_of_addOrderOf`. (`X_0(20)` and `X_0(24)`
  are genus-one curves of Mordell–Weil rank `0` whose `6`, resp. `8`,
  rational points are exactly their cusps; `X_0(35)` has genus `3` and
  `X_0(49)` genus `1`, again with only cuspidal rational points.)
* PRESENT in the list, shortcut UNAVAILABLE: `14, 15, 16, 18, 21, 25,
  27`. There a rational cyclic `n`-isogeny genuinely exists, so the
  isogeny is no contradiction at all and only the finer `X_1(n)`
  statement excludes the point. Witnesses, all exhibited with PARI/GP
  `ellisomat` (untrusted searcher, never a proof): `[1,−1,0,−2,−1]` of
  conductor `49`, degrees `{1,2,7,14}`; `[1,0,1,−1,−2]` of conductor
  `50`, degrees `{1,3,5,15}`; `[1,−1,0,0,−5]` of conductor `45`,
  degrees `{1,2,4,8,16}`; `[1,−1,1,−5,−7]` of conductor `126`, degrees
  `{1,2,3,6,9,18}`; `[1,−1,0,3,−1]` of conductor `162` for degree `21`;
  and the isogeny classes `11a` for degree `25`, `27a` for degree `27`.

This supersedes the two earlier partial statements of the criterion
that were recorded here on the same day — one naming only `35` and `49`
as available (it missed `20` and `24`, which are `> 19` and are none of
`21, 25, 27`, hence equally absent from the list), the other naming
only `14, 15, 16, 18, 25, 27` as unavailable. Both were correct as far
as they went, and both are subsumed by the criterion above.

The trade-off at the four `X_0` levels is deliberate and explicit:
Kenku's theorem is strictly STRONGER than each individual `X_1(n)`
statement it replaces, but it is one canonical, precisely citable
theorem instead of one ad-hoc citation per level, and the passage from
it to each level is proven rather than asserted.

SHARPENING (2026-07-25) of the four levels `14, 15, 16, 18` — where the
shortcut is unavailable but a genus-`0` fibre-product description
exists: each is now PROVEN from a level-structure leaf stated in the
shape the modular-curve literature uses, so that the surviving `sorry`
names the actual modular input rather than an order:

* `no_torsion_order_14` ⟸ `not_order_two_and_order_seven_point`
  (`X_1(2) ×_{X_1(1)} X_1(7)`),
* `no_torsion_order_15` ⟸ `not_order_three_and_order_five_point`
  (`X_1(3) ×_{X_1(1)} X_1(5)`),
* `no_torsion_order_16` ⟸ `not_halved_order_eight_point`
  (the halving cover `X_1(16) → X_1(8)`),
* `no_torsion_order_18` ⟸ `not_order_two_and_order_nine_point`
  (`X_1(2) ×_{X_1(1)} X_1(9)`).

Each derivation is pure `addOrderOf` bookkeeping (`addOrderOf_nsmul'`);
each leaf is equivalent to the order statement it replaces, but sits
over genus-`0` levels whose Tate normal forms are explicit, which is
where an elementary attack would have to begin. The genus values listed
above were recomputed from the formula on 2026-07-25 and all agree.

SHARPENING (2026-07-25, later pass) of level `27` — the one level in
Kenku's list where `X_0` still bites, because `X_0(27)` has genus `1`.
Being IN the list means the isogeny alone is no contradiction, but it
does not mean `X_0(27)` is useless: that curve is `27a1`, of
Mordell–Weil rank `0` with `X_0(27)(ℚ) ≅ ℤ/3` and exactly two rational
cusps, so it has exactly ONE non-cuspidal rational point and a rational
cyclic `27`-subgroup therefore PINS the `j`-invariant. Level `27` is
consequently PROVEN from two nodes,

* `j_of_stable_cyclic_subgroup_order_27` — the `X_0(27)` statement: a
  Galois-stable cyclic subgroup of order `27` forces
  `j(E) = −12288000`, the CM value of discriminant `−27`; PROVEN
  2026-07-26 over two moduli leaves (`exists_x0Nine_hauptmodul`,
  `exists_x0TwentySeven_point`, the latter PROVEN 2026-07-26 in turn
  over `exists_x0TwentySeven_moduliPoint`, which is PROVEN 2026-07-26
  over the level-`3` leaf `exists_x0Three_chainParameters`) plus the
  Mordell–Weil half
  `MazurLevel27.rational_point_x0TwentySeven`, which is mathlib's
  `fermatLastTheoremThree` because `X_0(27)` IS the Fermat cubic;
* `no_torsion_order_27_of_j` — stated as Olson's theorem that a CM
  elliptic curve over `ℚ` has torsion in
  `{ℤ/1, ℤ/2, ℤ/3, ℤ/4, ℤ/6, (ℤ/2)²}`, but PROVEN (2026-07-25) without
  any CM or reduction theory: the order-`9` point it produces forces the
  curve onto the genus-`0` curve `X_1(9)`, where `j = −12288000` becomes
  a degree-`36` polynomial equation in the Kubert parameter with no
  rational root (`MazurLevel27.jEquation_rat`, a congruence mod `2`),

in place of the former `X_1(27)` citation (genus `13`). Verified with
PARI/GP (untrusted searcher, statement check only): in the
conductor-`27` class the unique `27`-isogeny joins `[−2430, 184437/4]`
and `[−270, −6831/4]`, both of `j`-invariant `−12288000`; and the
squarefree twists `y² = x³ − 2430 d² x + (184437/4) d³`, `|d| ≤ 80`,
all have torsion trivial or `ℤ/3`.

The SAME sharpening is NOT available at levels `21` and `25`, because
there the isogeny does not pin `j`. `X_0(21)` has genus `1` but its
non-cuspidal rational points carry MORE THAN ONE `j`-invariant: a
PARI/GP `ellisomat` sweep over the models `[a₁,a₂,a₃,a₄,a₆]` with
`a₁, a₃ ∈ {0,1}`, `a₂ ∈ {−1,0,1}`, `a₄, a₆ ∈ [−40,40]` exhibits the two
values `j = −140625/8` and `j = 3375/2` with a rational cyclic
`21`-isogeny. `X_0(25)` has genus `0`, so it carries a whole rational
one-parameter family of them. Those two levels are therefore the only
bare sorry nodes left among the eleven.

Level `15` was taken one step further on 2026-07-25: the genus-`0` Tate
normal form its docstring named as missing is now BUILT and PROVEN (see
"Tate normal form at a rational point of order `5`" below), so
`not_order_three_and_order_five_point` is DERIVED and the surviving leaf
is `WeierstrassCurve.tateNF_self_no_order_three` — the single-parameter
statement that `y² + (1 − b) x y − b y = x³ − b x²` never has a rational
`3`-torsion point, which is `X_1(15)` itself. What that leaf still needs
is a rank-`0` Mordell–Weil computation, i.e. descent machinery mathlib
does not have.

A sweep over `≈ 4.8 · 10⁵` integral models with `|a₄|, |a₆| ≤ 100`
found exact rational point orders only in `{1, …, 10}`, consistent with
all eleven statements.
-/

/-!
##### The `X_0` node, split along its two literature citations (2026-07-25)

`mem_cyclicIsogenyDegrees` — the statement the four levels `20, 24, 35,
49` consume — is now PROVEN from the two theorems it was always a
merger of, each stated separately below over exactly the same
hypotheses:

* `prime_mem_cyclicIsogenyDegrees` — Mazur, *Rational isogenies of
  prime degree* (Invent. Math. 44, 1978), Thm 1: the PRIME degrees are
  `{2, 3, 5, 7, 11, 13, 17, 19, 37, 43, 67, 163}`.
* `composite_mem_cyclicIsogenyDegrees` — Kenku (1979–1982): the
  COMPOSITE degrees `≥ 20` are exactly `{21, 25, 27}`.

The split is an equivalence, not a weakening: each node is an instance
of the old statement, and the old statement is derived back from the
two (case split on `N.Prime`, with the range `0 < N < 20` discharged
outright, since `{1, …, 19}` lies in the list with nothing to prove).
Its point is attribution — the old single node forced one `sorry` to
carry two different citations, one of which (Mazur's) is also the
citation behind `no_prime_torsion_ge_eleven` (which moved BELOW on
2026-07-25 and is now PROVEN from this very node), so the tree now
shows that shared dependence instead of hiding it — as a real edge,
not only as a remark.

Note the asymmetry that makes the second node the smaller one: every
degree in Kenku's list that exceeds `19` is either prime (`37, 43, 67,
163`) or one of the three prime powers `21 = 3·7`, `25 = 5²`,
`27 = 3³`, so the composite node has to determine only those three.
-/

/-- **The isogeny character of a Galois-stable cyclic subgroup**
(PROVEN 2026-07-25): if a geometric point `g` of an elliptic curve
`E/ℚ` has exact finite order `N > 0` and its cyclic subgroup `⟨g⟩` is
stable under `Gal(ℚ̄/ℚ)`, then the Galois action on `⟨g⟩` is given by a
character

  `λ : Gal(ℚ̄/ℚ) → (ℤ/N)ˣ`,    `σ(g) = λ(σ) · g`.

This is the object every treatment of Mazur's theorem begins from — the
**isogeny character** of the `N`-isogeny `E → E/⟨g⟩` whose kernel is
`⟨g⟩` (Mazur, *Rational isogenies of prime degree*, §5; Serre,
*Propriétés galoisiennes*, §5.4).

Proof: `σ` carries `g` into `⟨g⟩`, so `σ(g) = k(σ) · g` for some integer
`k(σ)`, well defined modulo `N` because `addOrderOf g = N`
(`addOrderOf_dvd_iff_zsmul_eq_zero` against
`ZMod.intCast_zmod_eq_zero_iff_dvd`). Multiplicativity is
`Affine.Point.map_map` — the coercion of a product in
`Field.absoluteGaloisGroup ℚ` is the composite of the coercions — plus
additivity of `Affine.Point.map`. The identity of `Gal(ℚ̄/ℚ)` acts as
the identity on points, so `k(1) = 1` and hence `k(σ) k(σ⁻¹) = 1`,
which exhibits `k(σ)` as a unit without any appeal to `ZMod N` being a
field.

No primality is needed, only `0 < N`. That hypothesis is not cosmetic:
it is what makes `ZMod.val` a section of `ℕ → ZMod N`, which the
normalisation `λ(σ).val • g` in the conclusion requires. For `N = 0`
(a point of infinite order) `ZMod.val` is `Int.natAbs` and the
conclusion as stated would be FALSE, even though the character itself
still exists with values in `{±1}`. -/
theorem WeierstrassCurve.exists_isogenyCharacter (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (g : (E⁄(AlgebraicClosure ℚ)).Point) {N : ℕ}
    (hNpos : 0 < N) (hg : addOrderOf g = N)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    ∃ lam : Field.absoluteGaloisGroup ℚ →* (ZMod N)ˣ,
      ∀ σ : Field.absoluteGaloisGroup ℚ,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom g =
          ((lam σ : ZMod N).val) • g := by
  classical
  haveI : NeZero N := ⟨hNpos.ne'⟩
  -- The integer coefficient of a multiple of `g` is determined modulo `N`.
  have hiff : ∀ a b : ℤ, a • g = b • g ↔ (a : ZMod N) = (b : ZMod N) := by
    intro a b
    constructor
    · intro h
      have h0 : (a - b) • g = 0 := by rw [sub_zsmul, h, add_neg_cancel]
      have hd : (addOrderOf g : ℤ) ∣ (a - b) :=
        addOrderOf_dvd_iff_zsmul_eq_zero.mpr h0
      rw [hg] at hd
      have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (a - b) N).mpr hd
      rw [Int.cast_sub, sub_eq_zero] at hz
      exact hz
    · intro h
      have hz : ((a - b : ℤ) : ZMod N) = 0 := by rw [Int.cast_sub, h, sub_self]
      have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (a - b) N).mp hz
      rw [← hg] at hd
      have h0 := addOrderOf_dvd_iff_zsmul_eq_zero.mp hd
      rw [sub_zsmul, add_neg_eq_zero] at h0
      exact h0
  -- Galois moves `g` inside `⟨g⟩`; choose an integer coefficient for each `σ`.
  have hmem : ∀ σ : Field.absoluteGaloisGroup ℚ,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom g ∈
        AddSubgroup.zmultiples g :=
    fun σ => hstable σ g (AddSubgroup.mem_zmultiples g)
  choose k hk using fun σ => AddSubgroup.mem_zmultiples_iff.mp (hmem σ)
  -- The Galois action on points is a monoid action.
  have hcomp : ∀ σ τ : Field.absoluteGaloisGroup ℚ,
      ∀ P : (E⁄(AlgebraicClosure ℚ)).Point,
      Affine.Point.map
          ((σ * τ : Field.absoluteGaloisGroup ℚ) :
            AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom P =
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom
          (Affine.Point.map
            (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom P) := by
    intro σ τ P
    have hc : ((σ * τ : Field.absoluteGaloisGroup ℚ) :
          AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom =
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom.comp
          (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom :=
      AlgHom.ext fun x => rfl
    rw [Affine.Point.map_map, hc]
  -- Multiplicativity of the coefficient.
  have hmul : ∀ σ τ : Field.absoluteGaloisGroup ℚ,
      ((k (σ * τ) : ℤ) : ZMod N) = ((k σ : ℤ) : ZMod N) * ((k τ : ℤ) : ZMod N) := by
    intro σ τ
    have h1 : (k (σ * τ)) • g = (k σ * k τ) • g := by
      rw [hk (σ * τ), hcomp σ τ g, ← hk τ, map_zsmul, ← hk σ, smul_smul,
        mul_comm (k τ) (k σ)]
    have h2 := (hiff _ _).mp h1
    push_cast at h2
    exact h2
  -- The identity acts trivially, so the coefficient at `1` is `1`.
  have hmap1 : ∀ P : (E⁄(AlgebraicClosure ℚ)).Point,
      Affine.Point.map
        ((1 : Field.absoluteGaloisGroup ℚ) :
          AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom P = P := by
    intro P; cases P <;> rfl
  have hone : ((k 1 : ℤ) : ZMod N) = 1 := by
    have h1 : (k 1) • g = (1 : ℤ) • g := by rw [hk 1, one_zsmul, hmap1 g]
    have h2 := (hiff _ _).mp h1
    rwa [Int.cast_one] at h2
  -- Hence every coefficient is a unit, with inverse the coefficient at `σ⁻¹`.
  have hunit : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ((k σ : ℤ) : ZMod N) * ((k σ⁻¹ : ℤ) : ZMod N) = 1 := by
    intro σ
    rw [← hmul σ σ⁻¹, mul_inv_cancel, hone]
  refine ⟨MonoidHom.mk' (fun σ => ⟨((k σ : ℤ) : ZMod N), ((k σ⁻¹ : ℤ) : ZMod N),
      hunit σ, (mul_comm _ _).trans (hunit σ)⟩)
    (fun σ τ => Units.ext (by simpa using hmul σ τ)), ?_⟩
  intro σ
  rw [← hk σ, ← natCast_zsmul]
  refine (hiff _ _).mpr ?_
  simp [ZMod.natCast_val]

/-- **Mazur's rational isogenies of prime degree** (sorry node — the
prime half of the `X_0` input, restated 2026-07-25 in isogeny-character
form and narrowed to the range that is actually open): there is NO
elliptic curve `E/ℚ` carrying a geometric point `g` of exact prime order
`N ≥ 23` with `N ∉ {37, 43, 67, 163}` whose cyclic subgroup `⟨g⟩` is
Galois-stable — equivalently, whose isogeny character `λ` exists.

A Galois-stable subgroup of order `N` is the kernel of an `N`-isogeny
`E → E/⟨g⟩` defined over `ℚ` (Vélu), so this says exactly that
`X_0(N)(ℚ)` has no non-cuspidal point for such `N`. Mazur, "Rational
isogenies of prime degree" (Invent. Math. 44, 1978), Thm 1.

FAITHFULNESS OF THE RECUT. This node together with
`exists_isogenyCharacter` is EQUIVALENT to the single statement it
replaces (`prime_mem_cyclicIsogenyDegrees`, proven from it below), so
nothing was weakened and nothing strengthened:

* `hlam` and the old `hstable` imply each other — `hstable` follows from
  `hlam` because `σ(m·g) = m·σ(g) = (m λ(σ))·g` again lies in `⟨g⟩`, and
  `hlam` follows from `hstable` by the lemma above;
* the excluded range is exactly the old conclusion's list: the primes
  `< 23` are `2, 3, 5, 7, 11, 13, 17, 19`, and the remaining four are
  `37, 43, 67, 163`. Both ranges are discharged mechanically below, so
  the reduction is complete rather than partial.

What the recut buys is that the surviving `sorry` (a) names the isogeny
character, which is the object Mazur's §5 argument actually manipulates,
and (b) is a bounded-away non-existence statement over the range where
the argument has content, instead of a membership assertion quantified
over all primes.

IRREDUCIBLE at this mathlib pin: the proof is the Eisenstein-ideal
descent on `J_0(N)` — it studies the Eisenstein quotient of the
Jacobian, shows it has Mordell–Weil rank `0` over `ℚ`, and reads the
rational points of `X_0(N)` off that. No modular curve, no Jacobian and
no Hecke algebra exists in this development. The missing machinery, in
dependency order for whoever continues here: (1) the mod-`N` cyclotomic
character together with the Weil-pairing identity `λ · λ' = χ` on
`E[N]`, where `λ'` is the character on `E[N]/⟨g⟩`; (2) inertia at `N`
and Serre's theorem that `λ¹²` is unramified outside `N`, whence
`λ¹² = χ¹²ᵃ`; (3) `X_0(N)`, `J_0(N)`, the Hecke algebra and the
Eisenstein ideal. Steps (1)–(2) are Serre's reduction: they sharpen this
node but do not close it — historically they bounded `N` for curves
without CM and never yielded the exact list, which is precisely the gap
Mazur's Eisenstein-ideal argument filled — so (3) is the real
dependency.

This is the same theorem of Mazur that `no_prime_torsion_ge_eleven`
cites; the two nodes are stated separately because neither implies the
other (that one is about a rational POINT of order `ℓ`, i.e. `X_1(ℓ)`,
this one about a rational SUBGROUP, i.e. `X_0(N)`, and `X_1(ℓ) → X_0(ℓ)`
runs the wrong way to transfer the conclusion). -/
theorem WeierstrassCurve.not_isogenyCharacter_of_prime_ge_twentyThree
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) {N : ℕ}
    (hN : N.Prime) (hN23 : 23 ≤ N)
    (hNexc : N ∉ ({37, 43, 67, 163} : Finset ℕ))
    (hg : addOrderOf g = N)
    (lam : Field.absoluteGaloisGroup ℚ →* (ZMod N)ˣ)
    (hlam : ∀ σ : Field.absoluteGaloisGroup ℚ,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom g =
        ((lam σ : ZMod N).val) • g) :
    False :=
  sorry

/-- **Mazur's rational isogenies of prime degree** (PROVEN 2026-07-25
from the isogeny-character node above; the prime half of the `X_0`
input): if the cyclic subgroup `⟨g⟩` generated by a geometric point `g`
of an elliptic curve `E/ℚ` has exact order a PRIME `N` and is stable
under `Gal(ℚ̄/ℚ)`, then

  `N ∈ {2, 3, 5, 7, 11, 13, 17, 19, 37, 43, 67, 163}`.

The proof here is only the reduction to the open range: for `N < 23`
primality already forces `N ∈ {2, 3, 5, 7, 11, 13, 17, 19}`, all of
which are in the list, so there is nothing to prove; `37, 43, 67, 163`
are in the list outright; and for every other prime the isogeny
character produced by `exists_isogenyCharacter` contradicts
`not_isogenyCharacter_of_prime_ge_twentyThree`. The mathematical content
is entirely in that node. -/
theorem WeierstrassCurve.prime_mem_cyclicIsogenyDegrees (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (g : (E⁄(AlgebraicClosure ℚ)).Point) {N : ℕ}
    (hN : N.Prime) (hg : addOrderOf g = N)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    N ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 37, 43, 67, 163} : Finset ℕ) := by
  by_cases h23 : N < 23
  · have h0 := hN.two_le
    interval_cases N <;> revert hN <;> decide
  · by_cases hexc : N ∈ ({37, 43, 67, 163} : Finset ℕ)
    · fin_cases hexc <;> decide
    · exact absurd (E.exists_isogenyCharacter g hN.pos hg hstable)
        (by
          rintro ⟨lam, hlam⟩
          exact E.not_isogenyCharacter_of_prime_ge_twentyThree g hN
            (by omega) hexc hg lam hlam)

/-!
##### Kenku's composite node, split along divisor descent (2026-07-25)

`composite_mem_cyclicIsogenyDegrees` is now PROVEN from five shallower
nodes plus one piece of elementary machinery proven here.

The machinery is `exists_stable_zmultiples_of_dvd`: **the set of rational
cyclic isogeny degrees is closed under divisors.** If `⟨g⟩` is a
Galois-stable cyclic subgroup of order `N` and `d ∣ N`, then
`⟨(N/d) • g⟩` is a Galois-stable cyclic subgroup of order `d`. Both
halves are elementary and are proven in full: the order is
`addOrderOf_nsmul'` together with `Nat.gcd_eq_right` and
`Nat.div_div_self`, and stability holds because `σ` acts by an ADDITIVE
map, so `σ g = k • g` forces `σ (m • g) = m • (k • g) = k • (m • g)`.
(This is the subgroup-level form of the classical statement that a
cyclic `N`-isogeny factors through a cyclic `d`-isogeny for every
`d ∣ N`; note it needs stability of `⟨g⟩` only, not pointwise fixing.)

With divisor closure available, the two halves of Kenku's determination
become five separate literature nodes:

* the PRIME-POWER half. The prime powers occurring in the full
  Mazur–Kenku list `{1, …, 19, 21, 25, 27, 37, 43, 67, 163}` are
  `2, 4, 8, 16, 3, 9, 27, 5, 25, 7, 11, 13, 17, 19, 37, 43, 67, 163`,
  so the composite ones are exactly `4, 8, 9, 16, 25, 27`. The MINIMAL
  prime powers absent from the list are therefore `32 = 2⁵`,
  `81 = 3⁴`, `125 = 5³`, and `p²` for every prime `p ≥ 7` — four
  statements, from which divisor descent recovers the whole half:
  `not_cyclicIsogeny_thirtyTwo`, `not_cyclicIsogeny_eightyOne`,
  `not_cyclicIsogeny_oneHundredTwentyFive`,
  `not_cyclicIsogeny_sq_of_prime_ge_seven`.

  THREE of those four were themselves decomposed on 2026-07-26 and are now
  PROVEN rather than cited:

  - `not_cyclicIsogeny_thirtyTwo` over `exists_x0Sixteen_hauptmodul`
    (genus-`0` moduli at level `16`) and `exists_x0ThirtyTwo_point`
    (the degree-`2` degeneracy map), with the Mordell–Weil half of
    `X_0(32) : y² = x³ + 4x` PROVEN OUTRIGHT in
    `Fermat/FLT/FreyCurve/QuarticDescent.lean` from Fermat's quartic
    theorem `x⁴ − y⁴ ≠ z²`;
  - `not_cyclicIsogeny_eightyOne` over the single `j`-line leaf
    `not_cyclicIsogeny_eightyOne_of_j`, through the degree-`3` degeneracy
    map `X_0(81) → X_0(27)` and the PROVEN `X_0(27)` node
    `j_of_stable_cyclic_subgroup_order_27`, which pins `j = −12288000`.
    This replaces a Mordell–Weil computation on the genus-`4` curve
    `X_0(81)` by the fibre over one point. It became available only when
    the level-`27` cluster was HOISTED above this section (2026-07-26); it
    had been blocked purely by declaration order for a day;
  - `not_cyclicIsogeny_sq_of_prime_ge_seven` over
    `not_cyclicIsogeny_sq_of_isogenyPrime`, Mazur's prime node cutting the
    uniform `p ≥ 7` down to the nine primes
    `{7, 11, 13, 17, 19, 37, 43, 67, 163}`.

  The one still-cited level is `125`, the one with no shallower
  intermediate level (`X_0(25)` has genus `0`); see its docstring.
* the remaining half, `notPrimePow_mem_cyclicIsogenyDegrees`: a level
  with at least two distinct prime factors lies in
  `{6, 10, 12, 14, 15, 18, 21}` — exactly the non-prime-powers of the
  full list. This is where the bulk of Kenku's 1979–1982 work sits, and
  it is the one node of the five that is not a single modular curve; it
  was itself split along divisor descent on 2026-07-25 and is now PROVEN
  from twelve further nodes (one uniform statement about products of two
  distinct primes, and the eleven concrete levels
  `20, 24, 28, 30, 36, 42, 45, 50, 54, 63, 75`) — see the section note
  immediately above it.

The assembly is then pure arithmetic and is proven below: for `N ≥ 20`
non-prime a prime power `p ^ k` forces `k ≥ 2`, and `p ≥ 7` gives
`p² ∣ N`; `p = 5` gives `N = 25` or `125 ∣ N`; `p = 3` gives `N = 9`
(too small), `N = 27`, or `81 ∣ N`; `p = 2` gives `N ≤ 16` (too small)
or `32 ∣ N`. A non-prime-power `N ≥ 20` meets the seven-element list
above only in `21`.

Sanity-checked with PARI/GP (2026-07-25; untrusted searcher, never a
proof): `ellisomat` over the nonsingular members of the
`2 · 2 · 3 · 31² = 11532` models `[a₁,a₂,a₃,a₄,a₆]` with
`a₁, a₃ ∈ {0,1}`, `a₂ ∈ {−1,0,1}`, `a₄, a₆ ∈ [−15,15]` returns
cyclic isogeny degrees whose composite PRIME POWERS are exactly
`{4, 8, 9, 16, 25, 27}` and whose NON-prime-powers are exactly
`{6, 10, 12, 14, 15, 18, 21}` — the two conclusion sets below, hit on
the nose, with `32`, `81`, `125` and every `p²` for `p ≥ 7` absent.
-/

/-- **Divisor descent for Galois-stable cyclic subgroups: stability**
(PROVEN 2026-07-25). If `⟨g⟩` is stable under `Gal(ℚ̄/ℚ)` then so is
`⟨m • g⟩` for every `m`. The point is that `Affine.Point.map σ` is an
ADDITIVE map, so `σ g = k • g` (some `k : ℤ`, by stability of `⟨g⟩`)
propagates: `σ (j • (m • g)) = j • (m • (k • g)) = (j * k) • (m • g)`.
No pointwise fixing and no rationality of `g` is needed. -/
lemma WeierstrassCurve.stable_zmultiples_nsmul (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (g : (E⁄(AlgebraicClosure ℚ)).Point) (m : ℕ)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples (m • g),
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples (m • g) := by
  intro σ x hx
  obtain ⟨j, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp
    (hstable σ g (AddSubgroup.mem_zmultiples g))
  have hmap : Affine.Point.map
      (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom (j • (m • g))
      = (j * k) • (m • g) := by
    rw [map_zsmul, map_nsmul, ← hk, smul_comm m k g, smul_smul]
  rw [hmap]
  exact AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples _) _

/-- **Divisor descent for Galois-stable cyclic subgroups** (PROVEN
2026-07-25): the rational cyclic isogeny degrees are closed under
divisors. From a Galois-stable cyclic subgroup `⟨g⟩` of order `N` and a
divisor `d ∣ N`, the element `(N / d) • g` generates a Galois-stable
cyclic subgroup of order exactly `d` — the unique subgroup of order `d`
inside `⟨g⟩ ≅ ℤ/N`.

The order computation is `addOrderOf_nsmul'` (`addOrderOf (n • g) =
addOrderOf g / gcd (addOrderOf g) n`) with `n = N / d`, whose gcd with
`N` is `N / d` since `N / d ∣ N` (`Nat.gcd_eq_right`), followed by
`Nat.div_div_self`. Stability is `stable_zmultiples_nsmul`. -/
lemma WeierstrassCurve.exists_stable_zmultiples_of_dvd (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (g : (E⁄(AlgebraicClosure ℚ)).Point) {N d : ℕ}
    (hN : N ≠ 0) (hd : d ∣ N) (hg : addOrderOf g = N)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    ∃ g' : (E⁄(AlgebraicClosure ℚ)).Point, addOrderOf g' = d ∧
      ∀ σ : Field.absoluteGaloisGroup ℚ,
        ∀ x ∈ AddSubgroup.zmultiples g',
          Affine.Point.map
            (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
            AddSubgroup.zmultiples g' := by
  have hd0 : d ≠ 0 := by rintro rfl; exact hN (Nat.eq_zero_of_zero_dvd hd)
  have hq0 : N / d ≠ 0 := by
    have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hd)
      (Nat.pos_of_ne_zero hd0)
    omega
  refine ⟨(N / d) • g, ?_, E.stable_zmultiples_nsmul g (N / d) hstable⟩
  rw [addOrderOf_nsmul' g hq0, hg, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hd),
    Nat.div_div_self hd hN]

/-! ### `X_0(27)` is the Fermat cubic — the Mordell–Weil half, PROVEN

The two lemmas below are the *arithmetic* half of the `X_0(27)` node,
and they are PROVEN outright (2026-07-26) from mathlib's
`fermatLastTheoremThree`.

`X_0(27)` is the elliptic curve `27a1 : y² + y = x³ − 7`. Completing the
square gives `(2y + 1)² = 4x³ − 27`, and scaling by `16` gives
`(8y + 4)² = (4x)³ − 432`, i.e. `Y² = X³ − 432` — the standard
Weierstrass model of the Fermat cubic `x³ + y³ = z³`, under
`(X, Y) ↦ (36 + Y : 36 − Y : 6X)`. So the determination of
`X_0(27)(ℚ)` — the "rank `0`, torsion `ℤ/3`" input that Kenku's
argument needs — IS Fermat's Last Theorem for exponent `3`, and mathlib
has that theorem at this pin.

Re-derived here (2026-07-26) with PARI/GP as an untrusted searcher,
never a prover: `ellinit([0,0,1,0,-7])` and `ellinit([0,0,0,0,-432])`
both have conductor `27`, `j = 0`, and `elltors` returns `ℤ/3`,
generated by `(3, 4)` and `(12, 36)` respectively. The identity
`(40 + 8y)³ + (32 − 8y)³ = (24x)³ ⟺ y² + y = x³ − 7` used below is
checked by `ring` inside the proof, so nothing is taken on trust.

The `j`-invariant is read off the point through the degree-`36` modular
function `j : X_0(27) → X(1)`, which factors as
`X_0(27) →^{π₁, deg 3} X_0(9) →^{j₉, deg 12} X(1)`. Both factors are
explicit, and both were computed here from `q`-expansions with PARI/GP
and verified as power-series identities to `O(q^58)`:

* on `X_0(9)`, with the rational Hauptmodul
  `t = (η(τ)/η(9τ))³ = q⁻¹ − 3 + 5q² − 7q⁵ + ⋯`,

    `j = (t + 9)³ (t³ + 243t² + 2187t + 6561)³ / (t⁹ (t² + 9t + 27))`;

  the poles of the right-hand side are the four cusps of `X_0(9)`:
  `t = 0` (order `9`, the cusp `0`), the two conjugate roots of
  `t² + 9t + 27` (the two cusps of denominator `3`), and `t = ∞` (the
  cusp `∞`); `9 + 1 + 1 + 1 = 12` ✓.
* on `X_0(27) = 27a1`, with the modular parametrisation
  `elltaniyama(27a1)`, the pullback of that Hauptmodul is the
  degree-`3` function

    `t = (4 − 3x − y) / x`,

  whose polar divisor is the cusp `∞ = O` together with the two
  conjugate cusps of denominator `9`, which are the points `x = 0`
  (`y² + y + 7 = 0`, discriminant `−27`).

Evaluating at the three rational points of `27a1`:

| point       | `t`   | status                        |
|-------------|-------|-------------------------------|
| `O`         | `∞`   | the rational cusp `∞`         |
| `(3, −5)`   | `0`   | the rational cusp `0`         |
| `(3, 4)`    | `−3`  | the unique non-cuspidal point |

and `j₉(−3) = 6³ · 2160³ / (−177147) = −12288000` exactly, the CM value
of discriminant `−27` (checked by hand and by PARI/GP). The polynomial
`(s + 9)³ (s³ + 243s² + 2187s + 6561)³ + 12288000 · s⁹ (s² + 9s + 27)`
factors over `ℚ` as `(s + 3)(s² + 27)` times an irreducible degree-`9`
polynomial, so `s = −3` is its ONLY rational root — which is what makes
the level-`27` lifting leaf below well-posed. -/

namespace MazurLevel27

/-- **The rational points of `X_0(27) : y² + y = x³ − 7`** (PROVEN
2026-07-26 from mathlib's `fermatLastTheoremThree`): every rational
point of the affine curve `y² + y = x³ − 7` has `x = 3` and
`y ∈ {4, −5}`.

Together with the point at infinity these are the three points of
`X_0(27)(ℚ) ≅ ℤ/3`; this is the Mordell–Weil input of Kenku's
determination of `X_0(27)`, and it is *literally* Fermat's Last Theorem
for exponent `3`. The translation: put `a = 36 + Y`, `b = 36 − Y`,
`c = 6X` with `X = 4x`, `Y = 8y + 4`; then

  `a³ + b³ = 2·36³ + 6·36·Y² = 93312 + 216(X³ − 432) = (6X)³ = c³`.

FLT₃ over `ℚ` (`fermatLastTheoremFor_iff_rat`) forces one of `a, b, c`
to vanish. `c = 0` means `x = 0`, whence `(2y + 1)² = −27 < 0`,
impossible over `ℚ`. `a = 0` means `y = −5` and `b = 0` means `y = 4`;
either way `x³ = 27`, and `x³ − 27 = (x − 3)((x + 3/2)² + 27/4)` forces
`x = 3`. -/
theorem rational_point_x0TwentySeven (x y : ℚ) (h : y ^ 2 + y = x ^ 3 - 7) :
    x = 3 ∧ (y = 4 ∨ y = -5) := by
  have hFLT : FermatLastTheoremWith ℚ 3 :=
    fermatLastTheoremFor_iff_rat.mp fermatLastTheoremThree
  have key : (40 + 8 * y) ^ 3 + (32 - 8 * y) ^ 3 = (24 * x) ^ 3 := by
    linear_combination 13824 * h
  have hcube : ∀ z : ℚ, z ^ 3 = 27 → z = 3 := by
    intro z hz
    have h0 : (z - 3) * (z ^ 2 + 3 * z + 9) = 0 := by linear_combination hz
    rcases mul_eq_zero.mp h0 with h1 | h1
    · linarith
    · nlinarith [sq_nonneg (2 * z + 3)]
  by_cases hc : (24 : ℚ) * x = 0
  · exfalso
    have hx : x = 0 := by linarith
    subst hx
    have h7 : y ^ 2 + y = -7 := by linear_combination h
    nlinarith [sq_nonneg (2 * y + 1)]
  by_cases ha : (40 : ℚ) + 8 * y = 0
  · have hy : y = -5 := by linarith
    subst hy
    exact ⟨hcube x (by linear_combination -h), Or.inr rfl⟩
  by_cases hb : (32 : ℚ) - 8 * y = 0
  · have hy : y = 4 := by linarith
    subst hy
    exact ⟨hcube x (by linear_combination -h), Or.inl rfl⟩
  · exact absurd key (hFLT _ _ _ ha hb hc)

/-- **Reading the `j`-invariant off a rational point of `X_0(27)`**
(PROVEN 2026-07-26): if a rational number `J` is the value at `t` of the
`X_0(9)` modular function `j₉` (written denominator-free as
`J · t⁹(t² + 9t + 27) = (t + 9)³(t³ + 243t² + 2187t + 6561)³`), and `t`
is the image `(4 − 3x − y)/x` of a rational point `(x, y)` of
`X_0(27) : y² + y = x³ − 7` under the degeneracy map `π₁`, then
`J = −12288000`.

This is the whole Kenku conclusion once the moduli dictionary is in
place, and it is pure arithmetic. By `rational_point_x0TwentySeven` the
point is `(3, 4)` or `(3, −5)`, so `3t = −5 − y` gives `t = −3` or
`t = 0`.

* `t = 0` is the rational cusp `0` of `X_0(27)`, and it is excluded by
  the `j`-relation itself rather than by an extra hypothesis: at `t = 0`
  the left-hand side vanishes while the right-hand side is
  `9³ · 6561³ ≠ 0`. That is exactly how a pole of `j` encodes a cusp.
* `t = −3` is the unique non-cuspidal rational point, where the relation
  reads `J · (−177147) = 216 · 2160³ = 2176782336000`, i.e.
  `J = −12288000`.

Note that the point at infinity of `27a1` — the other rational cusp —
never arises, because the hypotheses speak of an affine point `(x, y)`. -/
theorem j_eq_of_x0TwentySeven_point (J x y t : ℚ)
    (hxy : y ^ 2 + y = x ^ 3 - 7)
    (ht : t * x = 4 - 3 * x - y)
    (hj : J * (t ^ 9 * (t ^ 2 + 9 * t + 27))
        = (t + 9) ^ 3 * (t ^ 3 + 243 * t ^ 2 + 2187 * t + 6561) ^ 3) :
    J = -12288000 := by
  obtain ⟨hx, hy⟩ := rational_point_x0TwentySeven x y hxy
  subst hx
  rcases hy with rfl | rfl
  · have htv : t = -3 := by linear_combination ht / 3
    subst htv
    have hlin : J * (-177147 : ℚ) = 2176782336000 := by linear_combination hj
    linarith
  · have htv : t = 0 := by linear_combination ht / 3
    subst htv
    exfalso
    norm_num at hj

end MazurLevel27

/-! ### `X_1(9) → X_0(9)`: the Kubert line, the diamond operator, and the
Hauptmodul

This block cuts `exists_x0Nine_hauptmodul` (below) into ONE proven
rational-function identity and TWO moduli leaves. All the explicit
formulae were found with PARI/GP (untrusted searcher, 2026-07-26) and
are re-verified here by `ring`.

THE GEOMETRY. `X_1(9)` and `X_0(9)` are both genus `0`. On `X_1(9)` the
Hauptmodul is the classical Kubert parameter `d` of the Tate normal form
`E(b, c) : y² + (1 − c)xy − by = x³ − bx²` with `(0,0)` of order `9`,
namely `c = d²(d − 1)`, `b = c(d² − d + 1)` (`MazurLevel18.exists_param`).
The covering `X_1(9) → X_0(9)` is the quotient by the diamond operators,
a cyclic group of order `3` — `(ℤ/9)ˣ/{±1} ≅ ℤ/3` — so it is a
`ℤ/3`-cover, and this is exactly why the Kubert parameter of a curve
with a rational cyclic `9`-SUBGROUP need not be rational: only the
subgroup, not a generator, is defined over `ℚ`.

THE DIAMOND OPERATOR IS `d ↦ (d − 1)/d`. Computed here (2026-07-26) by
running the Tate-normalisation algorithm on `(E(b,c), 2·(0,0))`: with
`2·(0,0) = (b, bc)`, translating that point to the origin, shearing by
`s = a₄'/a₃'` to kill `a₄`, and scaling by `u = a₃''/a₂''` gives
`b' = −(d⁴ − 3d³ + 4d² − 3d + 1)/d⁵`, `c' = −(d − 1)²/d³`, hence
`d' = c'²/(b' − c') = (d − 1)/d`. This Möbius map has order `3`
(`d ↦ (d−1)/d ↦ −1/(d−1) ↦ d`), matching `⟨2⟩` of order `6` in `(ℤ/9)ˣ`
acting through `(ℤ/9)ˣ/{±1}`; the same computation run on `−(0,0) = (0,b)`
returns `d` unchanged, confirming that `⟨−1⟩` acts trivially, as it must.

THE HAUPTMODUL. The invariants of `d ↦ (d − 1)/d` are generated by the
orbit sum `d + (d−1)/d − 1/(d−1) = (d³ − 3d + 1)/(d² − d)`, and the
normalisation that matches the `η`-quotient Hauptmodul
`t = (η(τ)/η(9τ))³` of `X_0(9)` is

    t = R(d) := 27 d(d − 1) / (d³ − 6d² + 3d + 1),

pinned by the cusps: `R` kills the orbit `{0, 1, ∞}` (the three cusps of
`X_1(9)` above the width-`9` cusp `t = 0`) and blows up exactly on
`d³ − 6d² + 3d + 1`, the orbit above `t = ∞`; the constant `27` is fixed
by `j₉(t) ~ 3²⁷/t⁹` against `j ~ −1/d⁹` at `d → 0`. `R ∘ γ = R` is a
two-line `ring` check: with `γ(d) = (d−1)/d`, the denominator satisfies
`γ*(d³ − 6d² + 3d + 1) = −(d³ − 6d² + 3d + 1)/d³` and the numerator
`γ*(27d(d−1)) = −27(d−1)/d²`.

WHY THE FINAL IDENTITY IS CHEAP. Writing `q = d³ − 6d² + 3d + 1`,
`m = 27d(d − 1)`, `e = d² − d + 1`, the three polynomials occurring in
`j₉` factor completely along the Kubert line:

    m + 9q                        = 9 (d³ − 3d² + 1)
    m³ + 243m²q + 2187mq² + 6561q³ = 6561 (d⁹ − 9d⁸ + 27d⁷ − 48d⁶ + 54d⁵
                                            − 45d⁴ + 27d³ − 9d² + 1)
    m² + 9mq + 27q²               = 27 e³

and `c₄(E(b,c))` factors as the PRODUCT of the first two cofactors,
`c₄ = (d³ − 3d² + 1)(d⁹ − 9d⁸ + 27d⁷ − 48d⁶ + 54d⁵ − 45d⁴ + 27d³ −
9d² + 1)` (`tateCurve_c₄`), while
`Δ(E(b,c)) = d⁹(d − 1)⁹e³q` (`tateCurve_Δ`, the `K`-generic form of
`MazurLevel18.delta_param`). Multiplying the target by `q¹²` therefore
turns it into `27¹⁰ · (j · Δ) = 3³⁰ · c₄³`, i.e. into `hj` itself. The
`q`-expansion cross-check of the whole `j`-map,
`j = (t+9)³(t³+243t²+2187t+6561)³ / (t⁹(t²+9t+27))` with
`t = (η(τ)/η(9τ))³`, was re-run here to `O(q⁵⁹)`.
-/

namespace MazurLevel9

/-- **The Tate normal form curve at Kubert parameter `d`**:
`E(b, c) : y² + (1 − c)xy − by = x³ − bx²` with `c = d²(d − 1)` and
`b = c(d² − d + 1)`. This is the universal elliptic curve over the
`X_1(9)` line, in the coordinates of `MazurLevel18.exists_param`, stated
over an arbitrary field so that it can be used over `ℚ̄`. -/
def tateCurve {K : Type*} [Field K] (d : K) : WeierstrassCurve K :=
  ⟨1 - d ^ 2 * (d - 1), -(d ^ 2 * (d - 1) * (d ^ 2 - d + 1)),
    -(d ^ 2 * (d - 1) * (d ^ 2 - d + 1)), 0, 0⟩

/-- **The discriminant along the `X_1(9)` line** (PROVEN): the `K`-generic
form of `MazurLevel18.delta_param`,
`Δ = d⁹(d − 1)⁹(d² − d + 1)³(d³ − 6d² + 3d + 1)`. The four factors are the
four cusp orbits: `d ∈ {0, 1}` and `d = ∞` lie over the width-`9` cusp
`t = 0`, the two roots of `d² − d + 1` are the fixed points of the diamond
operator and lie over the two conjugate cusps `t² + 9t + 27 = 0`, and the
three roots of `d³ − 6d² + 3d + 1` lie over `t = ∞`. -/
lemma tateCurve_Δ {K : Type*} [Field K] (d : K) :
    (tateCurve d).Δ
      = d ^ 9 * (d - 1) ^ 9 * (d ^ 2 - d + 1) ^ 3 * (d ^ 3 - 6 * d ^ 2 + 3 * d + 1) := by
  simp only [tateCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- **`c₄` along the `X_1(9)` line, FACTORED** (PROVEN):
`c₄ = (d³ − 3d² + 1)(d⁹ − 9d⁸ + 27d⁷ − 48d⁶ + 54d⁵ − 45d⁴ + 27d³ − 9d² + 1)`.
The factorisation is what makes `j9_of_tateParam` a `ring` identity rather
than a degree-`90` elimination: the two factors are exactly the cofactors of
`(t + 9)` and of `(t³ + 243t² + 2187t + 6561)` after clearing `q`. -/
lemma tateCurve_c₄ {K : Type*} [Field K] (d : K) :
    (tateCurve d).c₄
      = (d ^ 3 - 3 * d ^ 2 + 1) * (d ^ 9 - 9 * d ^ 8 + 27 * d ^ 7 - 48 * d ^ 6 + 54 * d ^ 5
          - 45 * d ^ 4 + 27 * d ^ 3 - 9 * d ^ 2 + 1) := by
  simp only [tateCurve, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

/-- **The `X_0(9)` `j`-map, pulled back to the Kubert line** (PROVEN
2026-07-26 — the whole algebraic content of `exists_x0Nine_hauptmodul`):
if `J` is the `j`-invariant of the Tate curve at Kubert parameter `d`
(written denominator-free as `J · Δ = c₄³`) and `t` is the Hauptmodul
value `R(d) = 27d(d − 1)/(d³ − 6d² + 3d + 1)` (written denominator-free as
`t · (d³ − 6d² + 3d + 1) = 27d(d − 1)`), then `J = j₉(t)` in the
denominator-free form
`J · t⁹(t² + 9t + 27) = (t + 9)³(t³ + 243t² + 2187t + 6561)³`.

Note that no nondegeneracy beyond `d³ − 6d² + 3d + 1 ≠ 0` is needed: that
one hypothesis is what makes `t` well defined, and everything else is the
`ring` identity `27¹⁰ c₄³ = 3³⁰ (d³ − 3d² + 1)³(d⁹ − ⋯ + 1)³`.

Stated over an arbitrary field because the consumer applies it over `ℚ̄`,
where the Kubert parameter of a curve with a rational cyclic `9`-subgroup
lives; the conclusion descends to `ℚ` because `t` does. -/
lemma j9_of_tateParam {K : Type*} [Field K] (d J t : K)
    (hq : d ^ 3 - 6 * d ^ 2 + 3 * d + 1 ≠ 0)
    (hj : J * (tateCurve d).Δ = (tateCurve d).c₄ ^ 3)
    (ht : t * (d ^ 3 - 6 * d ^ 2 + 3 * d + 1) = 27 * d * (d - 1)) :
    J * (t ^ 9 * (t ^ 2 + 9 * t + 27))
      = (t + 9) ^ 3 * (t ^ 3 + 243 * t ^ 2 + 2187 * t + 6561) ^ 3 := by
  rw [tateCurve_Δ, tateCurve_c₄] at hj
  refine mul_right_cancel₀ (pow_ne_zero 12 hq) ?_
  have hA : t ^ 9 * (d ^ 3 - 6 * d ^ 2 + 3 * d + 1) ^ 9 = 27 ^ 9 * (d ^ 9 * (d - 1) ^ 9) := by
    rw [← mul_pow, ht]; ring
  have hB : (t ^ 2 + 9 * t + 27) * (d ^ 3 - 6 * d ^ 2 + 3 * d + 1) ^ 2
      = 27 * (d ^ 2 - d + 1) ^ 3 := by
    linear_combination (t * (d ^ 3 - 6 * d ^ 2 + 3 * d + 1) + 27 * d * (d - 1)
      + 9 * (d ^ 3 - 6 * d ^ 2 + 3 * d + 1)) * ht
  have hC : (t + 9) * (d ^ 3 - 6 * d ^ 2 + 3 * d + 1) = 9 * (d ^ 3 - 3 * d ^ 2 + 1) := by
    linear_combination ht
  have hD : (t ^ 3 + 243 * t ^ 2 + 2187 * t + 6561) * (d ^ 3 - 6 * d ^ 2 + 3 * d + 1) ^ 3
      = 6561 * (d ^ 9 - 9 * d ^ 8 + 27 * d ^ 7 - 48 * d ^ 6 + 54 * d ^ 5 - 45 * d ^ 4
          + 27 * d ^ 3 - 9 * d ^ 2 + 1) := by
    linear_combination ((t * (d ^ 3 - 6 * d ^ 2 + 3 * d + 1)) ^ 2
      + t * (d ^ 3 - 6 * d ^ 2 + 3 * d + 1) * (27 * d * (d - 1)) + (27 * d * (d - 1)) ^ 2
      + 243 * (d ^ 3 - 6 * d ^ 2 + 3 * d + 1)
        * (t * (d ^ 3 - 6 * d ^ 2 + 3 * d + 1) + 27 * d * (d - 1))
      + 2187 * (d ^ 3 - 6 * d ^ 2 + 3 * d + 1) ^ 2) * ht
  have hLid : J * (t ^ 9 * (t ^ 2 + 9 * t + 27)) * (d ^ 3 - 6 * d ^ 2 + 3 * d + 1) ^ 12
      = J * (t ^ 9 * (d ^ 3 - 6 * d ^ 2 + 3 * d + 1) ^ 9)
          * ((t ^ 2 + 9 * t + 27) * (d ^ 3 - 6 * d ^ 2 + 3 * d + 1) ^ 2)
          * (d ^ 3 - 6 * d ^ 2 + 3 * d + 1) := by ring
  have hRid : (t + 9) ^ 3 * (t ^ 3 + 243 * t ^ 2 + 2187 * t + 6561) ^ 3
        * (d ^ 3 - 6 * d ^ 2 + 3 * d + 1) ^ 12
      = ((t + 9) * (d ^ 3 - 6 * d ^ 2 + 3 * d + 1)) ^ 3
          * ((t ^ 3 + 243 * t ^ 2 + 2187 * t + 6561)
              * (d ^ 3 - 6 * d ^ 2 + 3 * d + 1) ^ 3) ^ 3 := by ring
  rw [hLid, hRid, hA, hB, hC, hD]
  linear_combination (27 : K) ^ 10 * hj

/-! ### The Tate normal form over an ARBITRARY field

The block below is the field-generic re-basing of the `ℚ`-specific chain
`MazurLevel18.order_three_of_a₂_eq_zero`, `.tate_triple`, `.psi3_eq_zero`,
`.exists_param` together with `MazurLevel27.cFour_cube_eq`,
`.jInvariant_of_variableChange` and
`WeierstrassCurve.exists_tateNormalForm_jInvariant_of_order_nine`.
Nothing in any of those proofs uses the ordering or the arithmetic of `ℚ` —
they are pure field algebra — so every step transcribes verbatim except

* the two `linarith` steps (`hy0` in `order_three_of_a₂_eq_zero` and
  `ha3ne` in the Tate-normal-form theorem), which merely rearrange a linear
  equation and become `linear_combination`, since a general field is not
  ordered; and
* `MazurLevel27.jInvariant_of_variableChange`, which over `ℚ` has to
  transport `E.j` across `E ⇝ E⁄ℚ` and here does not, because the statement
  is about a curve over the working field itself.

BOOKKEEPING NOTE (2026-07-26). The `ℚ` versions listed above are NOT
deleted and NOT modified: they are live consumers' code owned elsewhere
(`exists_tateNormalForm_of_order_nine`,
`exists_tateNormalForm_jInvariant_of_order_nine`,
`no_torsion_order_27_of_j`, and the `X_1(18)` cluster), and several agents
were in flight in those regions when this block was written. A later
cleanup may replace each of them by an instantiation of its namesake here;
that is a refactor, not a leaf.

Why the re-basing is needed at all — and why `exists_tateParam` may NOT be
"simplified" back to `ℚ`: the covering `X_1(9) → X_0(9)` is a `ℤ/3`-cover,
so the Kubert parameter `d` of a curve with a `ℚ`-rational cyclic
`9`-SUBGROUP is in general irrational (twisting only controls the `±1`
part). Only the `X_0(9)`-Hauptmodul value `R(d)` descends to `ℚ`, and that
descent is the separate leaf `exists_rat_hauptmodul_of_stable`. -/

section GenericTateNormalForm

variable {K : Type*} [Field K] [DecidableEq K] {W : WeierstrassCurve.Affine K}

omit [DecidableEq K] in
/-- **`−(0,0) = (0, b)` in Tate normal form** (PROVEN): the generic-field
form of `MazurLevel18.negY_zero_zero`. -/
lemma negY_zero_zero {b : K} (h3 : W.a₃ = -b) : W.negY 0 0 = b := by
  rw [Affine.negY, h3]; ring

/-- **`a₂ = 0` in the partial normal form means `(0,0)` has order `3`**
(PROVEN): the generic-field form of
`MazurLevel18.order_three_of_a₂_eq_zero`. The only change is that the
`linarith` closing `a₃ ≠ 0` from `0 = −a₃` becomes a `linear_combination`,
`K` not being ordered. -/
lemma order_three_of_a₂_eq_zero (h2 : W.a₂ = 0) (h4 : W.a₄ = 0) (h3ne : W.a₃ ≠ 0)
    (hns : W.Nonsingular 0 0) :
    Point.some 0 0 hns + Point.some 0 0 hns + Point.some 0 0 hns = 0 := by
  have hn0 : W.negY 0 0 = -W.a₃ := by rw [Affine.negY]; ring
  have hy0 : (0 : K) ≠ W.negY 0 0 := by
    rw [hn0]; intro h; exact h3ne (by linear_combination h)
  have hL : W.slope 0 0 0 0 = 0 := by
    rw [Affine.slope_of_Y_ne rfl hy0, h4]; simp
  have hdbl : Point.some 0 0 hns + Point.some 0 0 hns = -Point.some 0 0 hns := by
    rw [Point.add_self_of_Y_ne hy0, Point.neg_some hns]
    exact Point.some_eq_some W (by simp only [Affine.addX, hL, h2]; ring)
      (by simp only [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY, hL, h2]; ring)
  rw [hdbl]; abel

section Tate

variable {b c : K}
  (h1 : W.a₁ = 1 - c) (h2 : W.a₂ = -b) (h3 : W.a₃ = -b) (h4 : W.a₄ = 0)

include h1 h2 h3 h4 in
/-- **`3 • (0,0) = (c, b − c)`** (PROVEN): the generic-field form of
`MazurLevel18.tate_triple`, transcribed verbatim. -/
lemma tate_triple (hb : b ≠ 0) (hns : W.Nonsingular 0 0) :
    ∃ (x₃ y₃ : K) (h₃ : W.Nonsingular x₃ y₃),
      Point.some 0 0 hns + Point.some 0 0 hns + Point.some 0 0 hns = Point.some x₃ y₃ h₃ ∧
        x₃ = c ∧ y₃ = b - c := by
  have hn0 : W.negY 0 0 = b := negY_zero_zero h3
  have hy0 : (0 : K) ≠ W.negY 0 0 := by rw [hn0]; exact fun h => hb h.symm
  have hL : W.slope 0 0 0 0 = 0 := by
    rw [Affine.slope_of_Y_ne rfl hy0, h4]; simp
  obtain ⟨x₂, y₂, h₂, hdbl, hx₂, hy₂⟩ :
      ∃ (x₂ y₂ : K) (h₂ : W.Nonsingular x₂ y₂),
        Point.some 0 0 hns + Point.some 0 0 hns = Point.some x₂ y₂ h₂ ∧
          x₂ = b ∧ y₂ = b * c :=
    ⟨_, _, _, Point.add_self_of_Y_ne hy0, by simp only [Affine.addX, hL, h2]; ring,
      by simp only [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY, hL, h1, h2, h3]; ring⟩
  have hx₂ne : x₂ ≠ 0 := by rw [hx₂]; exact hb
  have hL3 : W.slope x₂ 0 y₂ 0 = c := by
    rw [Affine.slope_of_X_ne hx₂ne, hx₂, hy₂]; field_simp; ring
  refine ⟨_, _, _, by rw [hdbl, Point.add_of_X_ne hx₂ne], ?_, ?_⟩
  · rw [hL3]; simp only [Affine.addX, hx₂, h1, h2]; ring
  · rw [hL3]
    simp only [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY, hx₂, hy₂, h1, h2, h3]
    ring

include h1 h2 h3 h4 in
/-- **The order-`9` condition in Tate normal form is `ψ₃(c) = 0`**
(PROVEN): the generic-field form of `MazurLevel18.psi3_eq_zero`,
transcribed verbatim. -/
lemma psi3_eq_zero (hb : b ≠ 0) (hns : W.Nonsingular 0 0)
    (h9 : (9 : ℕ) • Point.some 0 0 hns = 0) :
    c ^ 5 + c ^ 4 + (1 - b) * c ^ 3 - 3 * b * c ^ 2 + 3 * b ^ 2 * c - b ^ 3 = 0 := by
  obtain ⟨x₃, y₃, h₃, hR, hx₃, hy₃⟩ := tate_triple h1 h2 h3 h4 hb hns
  have hRRR : Point.some x₃ y₃ h₃ + Point.some x₃ y₃ h₃ + Point.some x₃ y₃ h₃ = 0 := by
    rw [← hR, ← h9]; abel
  have hRR : Point.some x₃ y₃ h₃ + Point.some x₃ y₃ h₃ = -Point.some x₃ y₃ h₃ :=
    add_eq_zero_iff_eq_neg.mp hRRR
  have hne : y₃ ≠ W.negY x₃ y₃ := by
    intro h
    have h0 : Point.some x₃ y₃ h₃ + Point.some x₃ y₃ h₃ = 0 := Point.add_self_of_Y_eq h
    rw [h0] at hRR
    exact Point.some_ne_zero _ (neg_eq_zero.mp hRR.symm)
  have hD : y₃ - W.negY x₃ y₃ = b - c - c ^ 2 := by
    rw [Affine.negY, h1, h3, hx₃, hy₃]; ring
  have hDne : b - c - c ^ 2 ≠ 0 := by rw [← hD]; exact sub_ne_zero.mpr hne
  have hM : W.slope x₃ x₃ y₃ y₃ = (2 * c ^ 2 - b * c - b + c) / (b - c - c ^ 2) := by
    rw [Affine.slope_of_Y_ne rfl hne, hD, hx₃, hy₃, h1, h2, h4]
    rw [div_eq_div_iff hDne hDne]; ring
  have hcond : W.addX x₃ x₃ (W.slope x₃ x₃ y₃ y₃) = x₃ :=
    (Point.some.inj ((Point.add_self_of_Y_ne (h₁ := h₃) hne).symm.trans
      (hRR.trans (Point.neg_some h₃)))).1
  rw [Affine.addX, hM, hx₃, h1, h2] at hcond
  have hpoly : (2 * c ^ 2 - b * c - b + c) ^ 2
      + (1 - c) * (2 * c ^ 2 - b * c - b + c) * (b - c - c ^ 2)
      + (b - 3 * c) * (b - c - c ^ 2) ^ 2 = 0 := by
    field_simp at hcond
    linear_combination hcond
  linear_combination -hpoly

end Tate

end GenericTateNormalForm

/-- **The `X_1(9)` parametrization is birational, over any field**
(PROVEN): the generic-field form of `MazurLevel18.exists_param`. On
`ψ₃(c) = 0` the Kubert parameter is `d = c²/(b − c)`; the excluded case
`b = c` forces `c⁵ = 0`. -/
lemma exists_param {K : Type*} [Field K] {b c : K} (hc : c ≠ 0)
    (h9 : c ^ 5 + c ^ 4 + (1 - b) * c ^ 3 - 3 * b * c ^ 2 + 3 * b ^ 2 * c - b ^ 3 = 0) :
    ∃ d : K, c = d ^ 2 * (d - 1) ∧ b = c * (d ^ 2 - d + 1) := by
  have hbc : b - c ≠ 0 := by
    intro h
    have hb' : b = c := sub_eq_zero.mp h
    rw [hb'] at h9
    exact hc (pow_eq_zero_iff (n := 5) (by norm_num) |>.mp (by linear_combination h9))
  refine ⟨c ^ 2 / (b - c), ?_, ?_⟩
  · field_simp
    linear_combination -h9
  · field_simp
    linear_combination -h9

/-- **`j · Δ = c₄³` over any field** (PROVEN): the generic-field form of
`MazurLevel27.cFour_cube_eq`, which is base-agnostic as written. -/
lemma cFour_cube_eq {K : Type*} [Field K] (V : WeierstrassCurve K) [V.IsElliptic] :
    V.j * V.Δ = V.c₄ ^ 3 := by
  rw [← WeierstrassCurve.coe_Δ', WeierstrassCurve.j, mul_comm, ← mul_assoc, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, one_mul]

/-- **The `j`-invariant survives the Tate normal form, over any field**
(PROVEN): the generic-field form of
`MazurLevel27.jInvariant_of_variableChange`. Simpler than its `ℚ`
namesake, which additionally has to cross `E ⇝ E⁄ℚ`. -/
lemma jInvariant_of_variableChange {K : Type*} [Field K] (V : WeierstrassCurve K) [V.IsElliptic]
    (C₁ C₂ : VariableChange K) (b c : K)
    [(⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve K).IsElliptic]
    (hEq : C₂ • (C₁ • V) = (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve K)) :
    V.j = (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve K).j := by
  simp_rw [← hEq, variableChange_j]

/-- **Tate normal form at a point of order `9`, over an ARBITRARY field,
recording the `j`-invariant** (PROVEN 2026-07-26): the generic-field form
of `WeierstrassCurve.exists_tateNormalForm_jInvariant_of_order_nine`,
transcribed verbatim except for the `linarith` step (`ha3ne`) and the
`j`-transport, as explained in the section note above.

Three changes of variables: translate `Q` to `(0,0)`, shear so that
`a₄ = 0`, then scale so that `a₂ = a₃`. The scaling is legitimate exactly
because `a₂ ≠ 0` after the shear, which is `order_three_of_a₂_eq_zero`
together with `addOrderOf Q = 9 ∤ 3`. -/
theorem exists_tateNF_of_order_nine {K : Type*} [Field K] [DecidableEq K]
    (V : WeierstrassCurve K) [V.IsElliptic] (Q : V.toAffine.Point) (hQ : addOrderOf Q = 9) :
    ∃ (b c : K) (_hb : b ≠ 0)
      (_hΔ : (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve K).Δ ≠ 0)
      (h00 : (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve K).toAffine.Nonsingular 0 0)
      (Ψ : V.toAffine.Point ≃+ (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve K).toAffine.Point),
      Ψ Q = Affine.Point.some 0 0 h00 ∧
        V.j * (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve K).Δ
          = (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve K).c₄ ^ 3 := by
  have hQ0 : Q ≠ 0 := by rintro rfl; simp at hQ
  obtain ⟨X, Y, hns, hQxy⟩ :
      ∃ (X Y : K) (h : V.toAffine.Nonsingular X Y), Q = Affine.Point.some X Y h := by
    rcases hcase : Q with _ | ⟨X, Y, h⟩
    · exact absurd hcase hQ0
    · exact ⟨X, Y, h, rfl⟩
  have hQ2 : Q + Q ≠ 0 := by
    intro h
    have hd : addOrderOf Q ∣ 2 := addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by rw [two_nsmul]; exact h)
    rw [hQ] at hd; norm_num at hd
  have hwne : Y ≠ V.toAffine.negY X Y := fun h =>
    hQ2 (by rw [hQxy]; exact Point.add_self_of_Y_eq h)
  have ha3ne : V.a₃ + X * V.a₁ + 2 * Y ≠ 0 := by
    intro h; exact hwne (by rw [Affine.negY]; linear_combination h)
  set s₀ : K := (V.a₄ + 2 * X * V.a₂ - Y * V.a₁ + 3 * X ^ 2)
      / (V.a₃ + X * V.a₁ + 2 * Y) with hs₀
  set C₁ : VariableChange K := ⟨1, X, s₀, Y⟩ with hC₁
  have hE1a₃ : (C₁ • V).a₃ = V.a₃ + X * V.a₁ + 2 * Y := by
    rw [WeierstrassCurve.variableChange_a₃, hC₁]; simp
  have hE1a₄ : (C₁ • V).a₄ = 0 := by
    rw [WeierstrassCurve.variableChange_a₄, hC₁]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    rw [hs₀]
    field_simp
    ring
  have hE1a₆ : (C₁ • V).a₆ = 0 := by
    have heq := hns.1
    rw [Affine.equation_iff] at heq
    rw [WeierstrassCurve.variableChange_a₆, hC₁]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    linear_combination -heq
  have h00' : (C₁ • V).toAffine.Nonsingular 0 0 :=
    Affine.nonsingular_zero.mpr ⟨hE1a₆, Or.inl (by rw [hE1a₃]; exact ha3ne)⟩
  have hmap : Point.equivVariableChange V C₁ (Point.some 0 0 h00') = Q := by
    rw [Point.equivVariableChange_some, hQxy]
    exact Point.some_eq_some _ (by simp [hC₁]) (by simp [hC₁])
  have ha2ne : (C₁ • V).a₂ ≠ 0 := by
    intro hz
    have h3P : Point.some 0 0 h00' + Point.some 0 0 h00' + Point.some 0 0 h00' = 0 :=
      order_three_of_a₂_eq_zero hz hE1a₄ (by rw [hE1a₃]; exact ha3ne) h00'
    have hQ3 : Q + Q + Q = 0 := by
      have hc := congrArg (Point.equivVariableChange V C₁) h3P
      rwa [map_add, map_add, map_zero, hmap] at hc
    have hd : addOrderOf Q ∣ 3 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by
        have e : (3 : ℕ) • Q = Q + Q + Q := by abel
        rw [e]; exact hQ3)
    rw [hQ] at hd; norm_num at hd
  set u : Kˣ := Units.mk0 ((C₁ • V).a₃ / (C₁ • V).a₂)
    (div_ne_zero (by rw [hE1a₃]; exact ha3ne) ha2ne)
  set C₂ : VariableChange K := ⟨u, 0, 0, 0⟩ with hC₂
  have huv : (u : K) = (C₁ • V).a₃ / (C₁ • V).a₂ := rfl
  have hune : (u : K) ≠ 0 := u.ne_zero
  set b : K := -(C₂ • (C₁ • V)).a₂ with hbdef
  set c : K := 1 - (C₂ • (C₁ • V)).a₁ with hcdef
  have hA4 : (C₂ • (C₁ • V)).a₄ = 0 := by
    rw [WeierstrassCurve.variableChange_a₄, hC₂]; simp [hE1a₄]
  have hA6 : (C₂ • (C₁ • V)).a₆ = 0 := by
    rw [WeierstrassCurve.variableChange_a₆, hC₂]; simp [hE1a₆]
  have hA23 : (C₂ • (C₁ • V)).a₃ = (C₂ • (C₁ • V)).a₂ := by
    rw [WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₂, hC₂]
    simp only [Units.val_inv_eq_inv_val]
    field_simp [huv]
    rw [huv]; field_simp
    ring
  have hA2v : (C₂ • (C₁ • V)).a₂ = ((u : K))⁻¹ ^ 2 * (C₁ • V).a₂ := by
    rw [WeierstrassCurve.variableChange_a₂, hC₂]; simp
  have hA2ne : (C₂ • (C₁ • V)).a₂ ≠ 0 := by
    rw [hA2v]; exact mul_ne_zero (pow_ne_zero 2 (inv_ne_zero hune)) ha2ne
  have hbne : b ≠ 0 := by rw [hbdef, neg_ne_zero]; exact hA2ne
  have hEq : C₂ • (C₁ • V) = (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve K) := by
    ext <;> simp [hbdef, hcdef, hA4, hA6, hA23]
  have h00'' : (C₂ • (C₁ • V)).toAffine.Nonsingular 0 0 :=
    Affine.nonsingular_zero.mpr ⟨hA6, Or.inl (by rw [hA23]; exact hA2ne)⟩
  have hΔE : V.Δ ≠ 0 := (WeierstrassCurve.isUnit_Δ (W := V)).ne_zero
  have hΔ2 : (C₂ • (C₁ • V)).Δ ≠ 0 := by
    rw [WeierstrassCurve.variableChange_Δ, WeierstrassCurve.variableChange_Δ]
    exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero _))
      (mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) hΔE)
  haveI hellW : (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve K).IsElliptic :=
    hEq ▸ (inferInstance : (C₂ • (C₁ • V)).IsElliptic)
  have hjW : V.j = (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve K).j :=
    jInvariant_of_variableChange V C₁ C₂ b c hEq
  have hjmul : V.j * (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve K).Δ
      = (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve K).c₄ ^ 3 := by
    rw [hjW]; exact cFour_cube_eq _
  refine ⟨b, c, hbne, hEq ▸ hΔ2, hEq ▸ h00'',
    (Point.equivVariableChange V C₁).symm.trans
      ((Point.equivVariableChange (C₁ • V) C₂).symm.trans (Point.equivOfEq hEq)), ?_, hjmul⟩
  have e1 : (Point.equivVariableChange V C₁).symm Q = Point.some 0 0 h00' := by
    rw [← hmap]; exact (Point.equivVariableChange V C₁).symm_apply_apply _
  have e2 : (Point.equivVariableChange (C₁ • V) C₂) (Point.some 0 0 h00'')
      = Point.some 0 0 h00' := by
    rw [Point.equivVariableChange_some]
    exact Point.some_eq_some _ (by simp [hC₂]) (by simp [hC₂])
  simp only [AddEquiv.trans_apply, e1, ← e2, AddEquiv.symm_apply_apply, Point.equivOfEq_some]

/-- **`d` is a Kubert parameter of the pair `(E, P)`**: the base change of
`E` to `ℚ̄` is isomorphic, as a group of points, to the Tate curve at `d`
by an isomorphism carrying `P` to `(0,0)`.

This is the `ℚ̄`-analogue of the conclusion of the PROVEN
`WeierstrassCurve.exists_tateNormalForm_of_order_nine`, packaged as a
predicate so that the two moduli leaves below can talk about the SAME
parameter. The Tate normal form of a pair `(E, P)` with `P` of order `9`
is unique, so `IsTateParam E P` is in fact a singleton; that uniqueness is
`isTateParam_unique` below.

Concretely the definition says: `C • (E⁄ℚ̄) = tateCurve d` for some
`C : VariableChange ℚ̄`, and `P` is the point `(C.r, C.t)` — which is exactly
`Point.equivVariableChange (E⁄ℚ̄) C (0,0) = P`, since that isomorphism sends
`(0,0)` to `(u²·0 + r, u³·0 + u²s·0 + t) = (r, t)`.

**FAITHFULNESS AUDIT — DEFINITION CORRECTED 2026-07-26. The previous version
made `exists_rat_hauptmodul_of_stable` FALSE AS STATED.** This predicate used
to read

    ∃ (h00 : (tateCurve d).toAffine.Nonsingular 0 0)
      (Ψ : (E⁄ℚ̄).Point ≃+ (tateCurve d).toAffine.Point), Ψ P = some 0 0 h00,

i.e. it asked only for an ABSTRACT ISOMORPHISM OF ABELIAN GROUPS. That
carries no geometry at all, and in particular it does not pin `d` down. For
an elliptic curve over `ℚ̄ = AlgebraicClosure ℚ` one has, as abstract groups,

    E(ℚ̄) ≅ (ℚ/ℤ)² ⊕ ℚ^(ℵ₀)

(divisible; torsion `(ℚ/ℤ)²`; countable; of infinite rank, Frey–Jarden), so
ANY two elliptic curves over `ℚ̄` have isomorphic groups of points, and
`Aut((ℚ/ℤ)²) = GL₂(Ẑ)` is transitive on elements of order `9` (`GL₂(ℤ/9)` is
transitive on primitive vectors of `(ℤ/9)²`). So the old `IsTateParam E P d`
held for EVERY `d` making `tateCurve d` nonsingular, whatever `E` and `P`
were, and it therefore said nothing.

EXPLICIT COUNTEREXAMPLE to the old form of the descent leaf. Take any `E/ℚ`
with a Galois-stable cyclic subgroup of order `9` (they exist — `9` is a
rational cyclic isogeny degree) and take `d = √2`. Then

* `tateCurve √2` is nonsingular: in `tateCurve_Δ` the factors are `d ≠ 0`,
  `d − 1 ≠ 0`, `d² − d + 1 = 3 − √2 ≠ 0` and
  `d³ − 6d² + 3d + 1 = 5√2 − 11 ≠ 0` (since `50 ≠ 121`);
* `(0,0)` has order exactly `9` there: `9 • (0,0) = 0` holds identically along
  the Kubert line, and order `3` would force `b = d²(d−1)(d²−d+1) = 0`;
* hence the OLD `IsTateParam E g √2` held, while
  `R(√2) = 27√2(√2 − 1)/(5√2 − 11) = (−324 + 27√2)/71` is IRRATIONAL, so no
  rational `t` satisfies the conclusion.

(Re-checked numerically with PARI/GP, 2026-07-26: `Δ ≈ −0.12725 ≠ 0`;
`3·(0,0) ≈ (0.82843, 0.48528) ≠ 0`; `9·(0,0)` overflows to the point at
infinity; `R(√2) ≈ −4.025580757970795`, agreeing with `(−324 + 27√2)/71`.)

The moral is the standard trap of this development in a new dress: a `≃+`
between groups of points is a fine CONCLUSION of an existence theorem — it is
all `exists_tateNormalForm_of_order_nine` claims — but is useless as a
HYPOTHESIS, because the geometry lives in the change of variables, not in the
abstract group. Compare the `𝒪ᵥ`-rule in `CLAUDE.md`: values descend, the
existence of a coordinate does not.

CONSEQUENCE FOR THE SIBLING `exists_tateParam`: its statement text is
unchanged but its obligation is now the correct, stronger one. This costs it
nothing mathematically — the ℚ-proof it re-bases
(`exists_tateNormalForm_of_order_nine`) constructs `C₁`, `C₂` explicitly and
merely discards them at the end; here it must return their product. -/
def IsTateParam (E : WeierstrassCurve ℚ) (P : (E⁄(AlgebraicClosure ℚ)).Point)
    (d : AlgebraicClosure ℚ) : Prop :=
  ∃ C : WeierstrassCurve.VariableChange (AlgebraicClosure ℚ),
    C • (E⁄(AlgebraicClosure ℚ)) = tateCurve d ∧
      ∃ h : (E⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular C.r C.t,
        P = Affine.Point.some C.r C.t h

/-- **Tate normal form over `ℚ̄` at a geometric point of order `9`**
(SORRY LEAF, re-opened at integration 2026-07-26 against the REPAIRED
`IsTateParam`): an elliptic curve over `ℚ` whose geometric points contain
a point `P` of order `9` acquires, over `ℚ̄`, a Kubert parameter `d` —
nondegenerate, and computing `j(E)`.

**WHY THIS IS OPEN AGAIN, AND WHAT IS LEFT.** This node HAD a complete
proof, but of the WEAKER, superseded form of `IsTateParam`, which asked
only for an abstract group isomorphism
`Ψ : (E⁄ℚ̄).Point ≃+ (tateCurve d).Point` carrying `P` to `(0,0)`. That
form is too weak to be the Tate normal form: it does not say the two
curves are related by a CHANGE OF VARIABLES at all, so nothing about the
diamond operator or Galois naturality can be read off it. `IsTateParam`
was accordingly repaired (same day) to carry the variable change itself,

  `∃ C : VariableChange ℚ̄, C • (E⁄ℚ̄) = tateCurve d ∧ P = some C.r C.t _`,

which is what `nondegenerate_of_isTateParam`, `isTateParam_unique`,
`isTateParam_two_nsmul`, `isTateParam_galois` and hence
`exists_rat_hauptmodul_of_stable` all consume. The old proof establishes
the old statement and does NOT establish this one, so it was not carried
over — see git history for it.

**The remaining work is small and is bookkeeping, not mathematics.**
`exists_tateNF_of_order_nine` already CONSTRUCTS the required change of
variables internally (`C₁ := ⟨1, X, s₀, Y⟩` and the two after it) and
then discards it, exposing only the induced `Ψ`. Widening that lemma's
conclusion to return the composite `C` — and `P = some C.r C.t _` in
place of `Ψ P = some 0 0 _` — closes this leaf immediately, since every
step of its proof already goes through `Point.equivVariableChange`.

**THE REST OF THIS NODE WAS A MECHANICAL GENERALISATION OF PROVEN CODE,
NOT NEW MATHEMATICS**, and that is exactly how it was done.
`WeierstrassCurve.exists_tateNormalForm_jInvariant_of_order_nine`
proves this over `ℚ`, and `MazurLevel18.exists_param` turns its
`(b, c)` into the Kubert `d`; both proofs are pure field algebra — three
changes of variables (`Point.equivVariableChange`) plus one
`field_simp`/`linear_combination`. What had to change was only the base,
`(E⁄ℚ)` ⇝ `(E⁄ℚ̄)`. The re-based chain is the `GenericTateNormalForm`
block above, and this proof is its instantiation at `K = ℚ̄`,
`V = E⁄ℚ̄`:

* `order_three_of_a₂_eq_zero`, `tate_triple`, `psi3_eq_zero`,
  `exists_param` — the `(b,c)`-to-`d` chain, now stated for
  `W : WeierstrassCurve.Affine K`;
* `cFour_cube_eq` and `jInvariant_of_variableChange`, and
  `WeierstrassCurve.map_j` to relate `E.j` to `(E⁄ℚ̄).j`, whence the
  `algebraMap` in the conclusion here;
* the two `linarith` steps became `linear_combination`, `ℚ̄` not being
  an ordered field.

`exists_param`'s excluded case `c = 0` is handled the same way it is over
`ℚ`: `c = 0` forces `b³ = 0` in `ψ₃(c) = 0`, contradicting `b ≠ 0`.

FAITHFULNESS: the statement is over `ℚ̄` and MUST NOT be "simplified" back
to `ℚ`. `X_1(9) → X_0(9)` is a `ℤ/3`-cover, so the Kubert parameter of a
curve with a `ℚ`-rational cyclic `9`-subgroup is in general irrational;
only `R(d)` descends, which is the separate leaf
`exists_rat_hauptmodul_of_stable`. Here `P` is a geometric point, so the
Tate normal form of `(E, P)` is defined over `ℚ̄` and over nothing
smaller in general.

The `(b, c)` of the normal form and the `d` of `tateCurve` are related by
`c = d²(d − 1)`, `b = c(d² − d + 1)`, so the curve
`⟨1 − c, −b, −b, 0, 0⟩` produced there is definitionally `tateCurve d`
once `d` is substituted; `tateCurve` is written out in `d` precisely so
that the two leaves here can share one object.

The parameter is NOT unique as stated — the three Kubert parameters
`d`, `(d−1)/d`, `−1/(d−1)` of the pairs `(E, P)`, `(E, 2P)`, `(E, 4P)` all
occur — which is precisely why the descent leaf below takes `d` as an
argument rather than re-choosing it. -/
theorem exists_tateParam (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄(AlgebraicClosure ℚ)).Point) (hP : addOrderOf P = 9) :
    ∃ d : AlgebraicClosure ℚ, IsTateParam E P d ∧ (tateCurve d).Δ ≠ 0 ∧
      algebraMap ℚ (AlgebraicClosure ℚ) E.j * (tateCurve d).Δ = (tateCurve d).c₄ ^ 3 :=
  sorry

/-- **A Kubert parameter is nondegenerate** (PROVEN 2026-07-26): if `d` is a
Kubert parameter of `(E, P)` then `d ≠ 0` and `d³ − 6d² + 3d + 1 ≠ 0`.

Both are read off `tateCurve_Δ`: the change of variables multiplies `Δ` by a
unit, so `Δ(tateCurve d) ≠ 0`, and `d` and `d³ − 6d² + 3d + 1` are two of its
four factors. The second is what makes the Hauptmodul value `R(d)` defined at
all, and the first is what makes the diamond operator `γ(d) = (d − 1)/d`
defined. -/
lemma nondegenerate_of_isTateParam {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {P : (E⁄(AlgebraicClosure ℚ)).Point} {d : AlgebraicClosure ℚ}
    (hd : IsTateParam E P d) :
    d ≠ 0 ∧ d ^ 3 - 6 * d ^ 2 + 3 * d + 1 ≠ 0 := by
  haveI : (E⁄(AlgebraicClosure ℚ)).IsElliptic :=
    inferInstanceAs (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).IsElliptic
  obtain ⟨C, hC, -⟩ := hd
  have hΔ : (tateCurve d).Δ ≠ 0 := by
    rw [← hC, WeierstrassCurve.variableChange_Δ]
    exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero _))
      (WeierstrassCurve.isUnit_Δ (W := (E⁄(AlgebraicClosure ℚ)))).ne_zero
  rw [tateCurve_Δ] at hΔ
  refine ⟨?_, ?_⟩
  · rintro rfl; exact hΔ (by ring)
  · intro h; exact hΔ (by rw [h]; ring)

/-- **Rigidity of the Tate normal form over `ℚ̄`** (sorry node, cut 2026-07-26
out of `exists_rat_hauptmodul_of_stable` — step 1 of its five-step argument):
the Kubert parameter of a pair `(E, P)` is UNIQUE, so `d` really is a
function `d(E, P)` of the pair.

This is the classical rigidity that makes the Tate normal form a normal form,
and it is pure field algebra. Given two admissible changes of variables
`C`, `C'` with `C • (E⁄ℚ̄) = tateCurve d`, `C' • (E⁄ℚ̄) = tateCurve d'` and
`(C.r, C.t) = P = (C'.r, C'.t)`, put `D := C' * C⁻¹`, so that
`D • tateCurve d = tateCurve d'` and `D` fixes the origin, i.e. `D.r = D.t = 0`.
With `r = t = 0` the change-of-variables formulas collapse to

    a₁' = u⁻¹(a₁ + 2s),  a₂' = u⁻²(a₂ − s a₁ − s²),
    a₃' = u⁻³ a₃,        a₄' = u⁻⁴(a₄ − s a₃),      a₆' = u⁻⁶ a₆,

and on `tateCurve d` one has `a₄ = a₆ = 0`, `a₂ = a₃ = −b` with
`b = d²(d − 1)(d² − d + 1) ≠ 0`. Then `a₄' = 0` forces `u⁻⁴ s b = 0`, hence
`s = 0`; and `a₂' = a₃'` forces `u⁻² b = u⁻³ b`, hence `u = 1`. So `D = 1`,
`tateCurve d = tateCurve d'`, and comparing coefficients gives `c = c'`,
`b = b'`, whence `d = c²/(b − c) = d'` (note `b − c = d³(d − 1)²` and
`c² = d⁴(d − 1)²`, both nonzero by `nondegenerate_of_isTateParam`).

The only Lean-side work is the `VariableChange` group arithmetic; there is no
new mathematics. Nothing here uses `P` beyond `C.r = C'.r`, `C.t = C'.t`,
which is `Affine.Point.some.inj` applied to the two descriptions of `P`. -/
theorem isTateParam_unique {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {P : (E⁄(AlgebraicClosure ℚ)).Point} {d d' : AlgebraicClosure ℚ}
    (hd : IsTateParam E P d) (hd' : IsTateParam E P d') : d = d' :=
  sorry

/-- **The diamond operator on the Kubert line** (sorry node, cut 2026-07-26
out of `exists_rat_hauptmodul_of_stable` — step 3 of its five-step argument,
and the ONLY computation in it): if `d` is a Kubert parameter of `(E, P)`
then `(d − 1)/d` is a Kubert parameter of `(E, 2P)`.

Stated denominator-free as `d' * d = d − 1`, which given `d ≠ 0`
(`nondegenerate_of_isTateParam`) is the same thing and saves the consumer a
division.

THE COMPUTATION, already carried out (PARI/GP, 2026-07-26; see the section
note above). On `E(b, c) = tateCurve d` one has `2 · (0,0) = (b, bc)`
(the `ℚ̄`-analogue of `tateNF_double` above). Re-run Tate normalisation on the
pair `(E(b,c), 2·(0,0))`: translate `(b, bc)` to the origin, shear by
`s = a₄'/a₃'` to kill `a₄`, scale by `u = a₃''/a₂''`. The result is
`b' = −(d⁴ − 3d³ + 4d² − 3d + 1)/d⁵`, `c' = −(d − 1)²/d³`, hence
`d' = c'²/(b' − c') = (d − 1)/d`. The same computation run on
`−(0,0) = (0, b)` returns `d` unchanged, confirming that `⟨−1⟩` acts trivially
— as it must, since `X_1(9) → X_0(9)` is the quotient by
`(ℤ/9)ˣ/{±1} ≅ ℤ/3` — and that `γ³ = id`, which is also visible directly:
`d ↦ (d−1)/d ↦ −1/(d−1) ↦ d`.

In Lean this is one explicit `VariableChange` (a product of three) applied to
`tateCurve d`, verified by `ext` + `field_simp` + `ring`, plus the transport
of `2 • P` along it. The nondegeneracy needed by the divisions is exactly
`nondegenerate_of_isTateParam` together with `d ≠ 1` (also a factor of `Δ`).

Consumers should note that iterating this three times must return `d`, which
is a useful consistency check on any candidate proof. -/
theorem isTateParam_two_nsmul {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {P : (E⁄(AlgebraicClosure ℚ)).Point} {d : AlgebraicClosure ℚ}
    (hd : IsTateParam E P d) :
    ∃ d' : AlgebraicClosure ℚ, IsTateParam E ((2 : ℕ) • P) d' ∧ d' * d = d - 1 :=
  sorry

/-- **Galois naturality of the Kubert parameter** (PROVEN 2026-07-26 — step 2
of the five-step argument of `exists_rat_hauptmodul_of_stable`): if `d` is a
Kubert parameter of `(E, P)` then `σ(d)` is a Kubert parameter of `(E, σP)`,
for every `σ ∈ Gal(ℚ̄/ℚ)`.

This is where it matters that `E` is defined over `ℚ`: applying `σ`
coefficientwise to the admissible change of variables `C` gives another
admissible change of variables `C.map σ`, and

    (C.map σ) • (E⁄ℚ̄) = (C.map σ) • ((E⁄ℚ̄).map σ) = (C • (E⁄ℚ̄)).map σ
                       = (tateCurve d).map σ = tateCurve (σ d),

the first equality being `WeierstrassCurve.map_baseChange` (`σ` fixes `ℚ`, so
it fixes the base-changed curve), the second `map_variableChange`, and the
last a coefficientwise computation. On points, `σ` sends `(C.r, C.t)` to
`(σ C.r, σ C.t) = ((C.map σ).r, (C.map σ).t)`, which is `Point.map_some` —
true by `rfl`.

Note this is exactly the step the OLD abstract-`≃+` definition of
`IsTateParam` could not support: an abstract group isomorphism has no
coefficients for `σ` to act on. -/
theorem isTateParam_galois {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {P : (E⁄(AlgebraicClosure ℚ)).Point} {d : AlgebraicClosure ℚ}
    (hd : IsTateParam E P d) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    IsTateParam E (Affine.Point.map σ.toAlgHom P) (σ d) := by
  obtain ⟨C, hC, h, hP⟩ := hd
  subst hP
  have hW : (E⁄(AlgebraicClosure ℚ)).map (σ.toAlgHom : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)
      = (E⁄(AlgebraicClosure ℚ)) := WeierstrassCurve.map_baseChange E σ.toAlgHom
  have htc : (tateCurve d).map (σ.toAlgHom : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)
      = tateCurve (σ d) := by
    ext <;> simp [tateCurve, WeierstrassCurve.map]
  refine ⟨C.map (σ.toAlgHom : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ), ?_, ?_⟩
  · calc C.map (σ.toAlgHom : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) • (E⁄(AlgebraicClosure ℚ))
        = C.map (σ.toAlgHom : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) •
            ((E⁄(AlgebraicClosure ℚ)).map
              (σ.toAlgHom : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) := by rw [hW]
      _ = (C • (E⁄(AlgebraicClosure ℚ))).map
            (σ.toAlgHom : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) :=
          WeierstrassCurve.map_variableChange ..
      _ = (tateCurve d).map (σ.toAlgHom : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) := by rw [hC]
      _ = tateCurve (σ d) := htc
  · exact ⟨_, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Galois descent for scalars** (PROVEN 2026-07-26): an element of `ℚ̄`
fixed by every element of `Gal(ℚ̄/ℚ)` is rational. This is
`InfiniteGalois.mem_range_algebraMap_iff_fixed` packaged with its `IsGalois`
instance.

The `set_option` is not a resource bump: `IsGalois ℚ (AlgebraicClosure ℚ)`
does not synthesize under the default `isDefEq` transparency at this pin
(neither do its two components `Normal` and `Algebra.IsSeparable`, even with
all of Mathlib imported — verified 2026-07-26), and the two other uses of
this lemma in this file (`exists_point_eq_baseChange_of_fixed` and the
cyclotomic-character argument) are both already under the same option for the
same reason. Isolating it in a three-line lemma keeps it off the large
declaration below. -/
lemma exists_rat_of_galois_fixed (x : AlgebraicClosure ℚ)
    (hfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ x = x) :
    ∃ t : ℚ, algebraMap ℚ (AlgebraicClosure ℚ) t = x := by
  have hrat : x ∈ Set.range (algebraMap ℚ (AlgebraicClosure ℚ)) :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed x).mpr hfix
  obtain ⟨t, ht⟩ := hrat
  exact ⟨t, ht⟩

/-- **The Hauptmodul of a Galois-stable cyclic `9`-subgroup is RATIONAL**
(PROVEN 2026-07-26 over the three leaves just above — the moduli content
proper at level `9`): if `⟨g⟩` is a `Gal(ℚ̄/ℚ)`-stable cyclic subgroup of order `9`
of `E(ℚ̄)` and `d` is a Kubert parameter of `(E, g)`, then the Hauptmodul
value `R(d) = 27d(d − 1)/(d³ − 6d² + 3d + 1)` lies in `ℚ`.

THIS IS THE `ℤ/3`-DESCENT ALONG `X_1(9) → X_0(9)`, and it is the only
genuinely modular step left at this level. The argument, in full:

1. *Uniqueness.* The Tate normal form of `(E, P)` at a point of order `9`
   is unique: `a₆ = 0` fixes the translation, `a₄ = 0` fixes the shear,
   and `a₂ = a₃` fixes the scaling `u` (up to nothing, since `u = a₃'/a₂'`
   is determined). Hence `b`, `c`, and therefore `d = c²/(b − c)`, are
   FUNCTIONS of the isomorphism class of `(E, P)`. Write `d(E, P)`.
2. *Galois naturality.* `E` is defined over `ℚ`, so `σ` carries the normal
   form of `(E, P)` to the normal form of `(E, σP)`, whence
   `σ(d(E, P)) = d(E, σP)`.
3. *Diamond equivariance.* `d(E, 2P) = (d(E, P) − 1)/d(E, P)` — the
   computation recorded in the section note above, valid identically on
   the universal family, hence for every `(E, P)`.
4. *The character.* Stability of `⟨g⟩` gives
   `σ(g) = λ(σ) • g` with `λ(σ) ∈ (ℤ/9)ˣ` (`exists_isogenyCharacter`, PROVEN
   above); `(ℤ/9)ˣ = ⟨2⟩`, so `σ(g) = 2ᵏ • g` and, by 2–3,
   `σ(d) = γᵏ(d)` with `γ(d) = (d − 1)/d`.
5. *Invariance.* `R ∘ γ = R` (`ring`), so `σ(R(d)) = R(d)` for every
   `σ ∈ Gal(ℚ̄/ℚ)`, and the fixed field of the absolute Galois group acting
   on `ℚ̄` is `ℚ`. Hence `R(d) ∈ ℚ`.

WHAT IS PROVEN HERE AND WHAT IS LEFT. The assembly of all five steps is
written out below and compiles; steps 2, 4 and 5 are proven outright
(`isTateParam_galois`; `exists_isogenyCharacter` plus the `decide` that `2`
generates `(ℤ/9)ˣ`; `InfiniteGalois.mem_range_algebraMap_iff_fixed`), and so
is the `R ∘ γ = R` identity — carried here in its denominator-free form
`27 e(e−1) q(d) = 27 d(d−1) q(e)` and discharged by `linear_combination`
inside the induction on `k`. What remains open is exactly the two leaves
above: `isTateParam_unique` (step 1, rigidity) and `isTateParam_two_nsmul`
(step 3, the diamond). Both are pure field algebra with no modular input.

The conclusion is stated denominator-free, `t · (d³ − 6d² + 3d + 1) =
27d(d − 1)`, so that it does not have to carry the nonvanishing of the
denominator; the consumer has it from `Δ ≠ 0`.

FAITHFULNESS: this statement was FALSE as originally written, because
`IsTateParam` was an abstract group isomorphism. See the `IsTateParam`
docstring above for the explicit counterexample (`d = √2`) and the repair. -/
theorem exists_rat_hauptmodul_of_stable (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) (hg : addOrderOf g = 9)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g)
    (d : AlgebraicClosure ℚ) (hd : IsTateParam E g d) :
    ∃ t : ℚ, algebraMap ℚ (AlgebraicClosure ℚ) t * (d ^ 3 - 6 * d ^ 2 + 3 * d + 1)
      = 27 * d * (d - 1) := by
  classical
  obtain ⟨-, hqd⟩ := nondegenerate_of_isTateParam hd
  -- STEPS 1 + 3: the diamond orbit of `d`, with the Hauptmodul value constant along it.
  have key : ∀ k : ℕ, ∃ e : AlgebraicClosure ℚ,
      IsTateParam E ((2 ^ k : ℕ) • g) e ∧
      27 * e * (e - 1) * (d ^ 3 - 6 * d ^ 2 + 3 * d + 1)
        = 27 * d * (d - 1) * (e ^ 3 - 6 * e ^ 2 + 3 * e + 1) := by
    intro k
    induction k with
    | zero => exact ⟨d, by simpa using hd, by ring⟩
    | succ k ih =>
        obtain ⟨e, he, hR⟩ := ih
        obtain ⟨he0, -⟩ := nondegenerate_of_isTateParam he
        obtain ⟨e', he', hee⟩ := isTateParam_two_nsmul he
        refine ⟨e', ?_, ?_⟩
        · have h2 : ((2 ^ (k + 1) : ℕ)) • g = (2 : ℕ) • ((2 ^ k : ℕ) • g) := by
            rw [← mul_nsmul']
            congr 1
            ring
          rw [h2]
          exact he'
        · -- `R ∘ γ = R`, cleared of denominators: `q(γ e) = −q(e)/e³` and
          -- `27 γe (γe − 1) = −27(e − 1)/e²`.
          refine mul_right_cancel₀ (pow_ne_zero 3 he0) ?_
          have h2 : (e' * e) ^ 2 = (e - 1) ^ 2 := by rw [hee]
          have h3 : (e' * e) ^ 3 = (e - 1) ^ 3 := by rw [hee]
          linear_combination (27 * (d ^ 3 - 6 * d ^ 2 + 3 * d + 1) * e) * h2
            - (27 * (d ^ 3 - 6 * d ^ 2 + 3 * d + 1) * e ^ 2) * hee
            - (27 * d * (d - 1)) * h3 + (6 * (27 * d * (d - 1)) * e) * h2
            - (3 * (27 * d * (d - 1)) * e ^ 2) * hee - hR
  -- STEP 4: the isogeny character, and `2` generates `(ℤ/9)ˣ`.
  obtain ⟨lam, hlam⟩ := E.exists_isogenyCharacter g (by norm_num) hg hstable
  have hpow : ∀ n : ℕ, ((n : ZMod 9)).val • g = n • g := by
    intro n
    rw [ZMod.val_natCast, ← hg]
    exact mod_addOrderOf_nsmul g n
  have hgen : ∀ u : (ZMod 9)ˣ, ∃ k ∈ Finset.range 6, (u : ZMod 9) = 2 ^ k := by decide
  -- STEP 5: the Hauptmodul value is Galois-fixed, hence rational.
  set S : AlgebraicClosure ℚ := 27 * d * (d - 1) / (d ^ 3 - 6 * d ^ 2 + 3 * d + 1) with hSdef
  have hfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ S = S := by
    intro σ
    obtain ⟨k, -, hk⟩ := hgen (lam σ)
    have hσg : Affine.Point.map σ.toAlgHom g = (2 ^ k : ℕ) • g := by
      have h := hlam σ
      rw [hk, show ((2 : ZMod 9) ^ k) = (((2 ^ k : ℕ) : ℕ) : ZMod 9) from by push_cast; ring,
        hpow] at h
      exact h
    obtain ⟨e, he, hRe⟩ := key k
    have hσd : σ d = e := isTateParam_unique (hσg ▸ isTateParam_galois hd σ) he
    obtain ⟨-, hqe⟩ := nondegenerate_of_isTateParam he
    rw [hSdef, map_div₀]
    have h1 : σ (27 * d * (d - 1)) = 27 * e * (e - 1) := by
      simp only [map_mul, map_sub, map_one, map_ofNat, hσd]
    have h2 : σ (d ^ 3 - 6 * d ^ 2 + 3 * d + 1) = e ^ 3 - 6 * e ^ 2 + 3 * e + 1 := by
      simp only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat, hσd]
    rw [h1, h2, div_eq_div_iff hqe hqd]
    linear_combination hRe
  obtain ⟨t, ht⟩ := exists_rat_of_galois_fixed S hfix
  refine ⟨t, ?_⟩
  rw [ht, hSdef]
  exact div_mul_cancel₀ _ hqd

end MazurLevel9

/-- **`X_0(9)`, the genus-`0` level: a rational cyclic `9`-subgroup puts
`j` on the explicit degree-`12` Hauptmodul curve** (PROVEN 2026-07-26 over
the two `MazurLevel9` moduli leaves — the
moduli content at level `9`, introduced 2026-07-26): if the geometric
points of an elliptic curve over `ℚ` contain a point `g` of order `9`
whose cyclic subgroup is `Gal(ℚ̄/ℚ)`-stable, then there is a rational
number `t` with

  `j(E) · t⁹(t² + 9t + 27) = (t + 9)³(t³ + 243t² + 2187t + 6561)³`.

This is the statement that `(E, ⟨g⟩)` is a non-cuspidal rational point
of `X_0(9)`, together with the explicit `j`-map of that modular curve.
`X_0(9)` has **genus `0`** with a `ℚ`-rational cusp, so it is
`ℙ¹_ℚ`, and its Hauptmodul `t = (η(τ)/η(9τ))³` is defined over `ℚ`; a
rational point therefore has a rational `t`-coordinate, and `t ≠ 0`
(the cusp `0`) is forced by the displayed identity itself, whose
right-hand side does not vanish at `t = 0`.

The rational function was computed here (2026-07-26) from
`q`-expansions and verified as a power-series identity to `O(q^60)`;
see the section note above. Independently sanity-checked with PARI/GP:
for each of `t = 1, …, 5` the curve `ellfromj(j₉(t))` has cyclic
isogeny degrees `{1, 3, 9}`, and `j₉(−3) = −12288000`, whose curve has
degrees `{1, 3, 9, 27}`.

**PROVEN 2026-07-26 over the `MazurLevel9` block above**, whose section
note carries the geometry. The cut runs through the Kubert line of
`X_1(9)`, NOT through Vélu: `X_0(9) = X_1(9)/⟨diamond⟩` with the diamond
operator acting as the order-`3` Möbius map `γ(d) = (d − 1)/d`, and the
Hauptmodul is the invariant `R(d) = 27d(d − 1)/(d³ − 6d² + 3d + 1)`. What
is left open is exactly three things (updated 2026-07-26, when
`exists_rat_hauptmodul_of_stable` was PROVEN over two smaller leaves after
its `IsTateParam` hypothesis had to be repaired — see that docstring):

* `MazurLevel9.exists_tateParam` — the Tate normal form over `ℚ̄`, a
  mechanical re-basing of the PROVEN
  `exists_tateNormalForm_jInvariant_of_order_nine`. It was briefly PROVEN
  against the pre-repair `IsTateParam`, which asked only for an abstract
  group isomorphism; against the repaired statement, which carries the
  CHANGE OF VARIABLES, it is open again and needs only
  `exists_tateNF_of_order_nine` to stop discarding the variable change it
  already builds. See its docstring;
* `MazurLevel9.isTateParam_unique` — rigidity of the Tate normal form, i.e.
  that the Kubert parameter is a function of the pair `(E, P)`;
* `MazurLevel9.isTateParam_two_nsmul` — the diamond operator
  `d(E, 2P) = (d(E,P) − 1)/d(E,P)`, one explicit change of variables.

The `ℤ/3`-descent `X_1(9) → X_0(9)` itself —
`MazurLevel9.exists_rat_hauptmodul_of_stable`, the modular content proper at
this level — is PROVEN over those two, together with the PROVEN
`MazurLevel9.isTateParam_galois` (Galois naturality).

`MazurLevel9.exists_tateParam` — the Tate normal form over `ℚ̄` — is now
PROVEN (2026-07-26), by re-basing the `ℚ` chain
`exists_tateNormalForm_jInvariant_of_order_nine` + `MazurLevel18.exists_param`
to an arbitrary field; see the `GenericTateNormalForm` block in
`MazurLevel9`.

The `j`-map identity itself, which was the reason to fear this node, is
PROVEN: `MazurLevel9.j9_of_tateParam`. Compare `MazurLevel18.exists_param`,
which is the `X_1(9)` half of the same picture and is what
`exists_tateParam` re-runs over `ℚ̄`. -/
theorem WeierstrassCurve.exists_x0Nine_hauptmodul
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) (hg : addOrderOf g = 9)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    ∃ t : ℚ, E.j * (t ^ 9 * (t ^ 2 + 9 * t + 27))
      = (t + 9) ^ 3 * (t ^ 3 + 243 * t ^ 2 + 2187 * t + 6561) ^ 3 := by
  obtain ⟨d, hd, hΔ, hj⟩ := MazurLevel9.exists_tateParam E g hg
  obtain ⟨t, ht⟩ := MazurLevel9.exists_rat_hauptmodul_of_stable E g hg hstable d hd
  refine ⟨t, ?_⟩
  have hq : d ^ 3 - 6 * d ^ 2 + 3 * d + 1 ≠ 0 := by
    intro h
    exact hΔ (by rw [MazurLevel9.tateCurve_Δ, h]; ring)
  have key := MazurLevel9.j9_of_tateParam d (algebraMap ℚ (AlgebraicClosure ℚ) E.j)
    (algebraMap ℚ (AlgebraicClosure ℚ) t) hq hj ht
  refine (algebraMap ℚ (AlgebraicClosure ℚ)).injective ?_
  simpa only [map_mul, map_pow, map_add, map_ofNat] using key

namespace MazurLevel27

/-! ### Sharpness of the `X_0(9)` fibre over the CM point `j = −12288000`

The level-`27` hypothesis "`t` lies over `j(E)` under the degree-`12`
map `j₉`" only pins `t` down because the fibre of `j₉` over the CM value
`j = −12288000` contains a **single** rational point. The three lemmas
below prove exactly that, so it is no longer a PARI/GP claim in a
docstring but a theorem: the degree-`12` numerator

  `P(s) = (s + 9)³(s³ + 243s² + 2187s + 6561)³ + 12288000·s⁹(s² + 9s + 27)`

factors over `ℤ` as `(s + 3)(s² + 27)·Q(s)` with `Q` monic of degree `9`
and constant term `3²⁶` — an identity checked by `ring` in
`x0Nine_fibre_over_CM` — and `Q` has no rational root. The rational-root
step is a congruence rather than a divisor search: homogenising
`s = N/D` with `gcd(N, D) = 1`, `Q(N, D) mod 7` is

  `N⁹ + N⁸D + 3N⁷D² + N⁶D³ + 4N⁵D⁴ + 6N⁴D⁵ + 2N³D⁶ + 4N²D⁷ + 2ND⁸ + 2D⁹`,

which is nonzero at all `48` nonzero residue pairs — `p = 7` is the
smallest prime with that property (`p = 2, 3, 5` all fail; note `Q ≡ s⁹`
mod `3`). This is the same shape of argument as `jEquation_zmodTwo`
above, one level up. -/

/-- **The `mod 7` obstruction on the degree-`9` factor** (PROVEN by
`decide`): the homogenised degree-`9` cofactor `Q(N, D)` of the
`j₉`-fibre polynomial over `−12288000` is nonzero at every pair of
residues mod `7` other than `(0, 0)`. -/
lemma x0NineFibre_zmodSeven : ∀ n e : ZMod 7, ¬ (n = 0 ∧ e = 0) →
    (n ^ 9 + 12288753 * n ^ 8 * e + 73929348 * n ^ 7 * e ^ 2
        - 199113228 * n ^ 6 * e ^ 3 - 1463588514 * n ^ 5 * e ^ 4
        + 24020070318 * n ^ 4 * e ^ 5 + 255697522740 * n ^ 3 * e ^ 6
        + 1129718145924 * n ^ 2 * e ^ 7 + 2541865828329 * n * e ^ 8
        + 2541865828329 * e ^ 9) ≠ 0 := by
  decide

/-- **The degree-`9` cofactor has no primitive integral zero** (PROVEN):
immediate from `x0NineFibre_zmodSeven` by reduction modulo `7`. -/
lemma x0NineFibre_int (N D : ℤ) (h7 : ¬ ((7 : ℤ) ∣ N ∧ (7 : ℤ) ∣ D)) :
    (N ^ 9 + 12288753 * N ^ 8 * D + 73929348 * N ^ 7 * D ^ 2
        - 199113228 * N ^ 6 * D ^ 3 - 1463588514 * N ^ 5 * D ^ 4
        + 24020070318 * N ^ 4 * D ^ 5 + 255697522740 * N ^ 3 * D ^ 6
        + 1129718145924 * N ^ 2 * D ^ 7 + 2541865828329 * N * D ^ 8
        + 2541865828329 * D ^ 9 : ℤ) ≠ 0 := by
  intro hz
  refine x0NineFibre_zmodSeven (N : ZMod 7) (D : ZMod 7) ?_ ?_
  · rintro ⟨hn, hd⟩
    exact h7 ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd N 7).mp hn,
      (ZMod.intCast_zmod_eq_zero_iff_dvd D 7).mp hd⟩
  · have := congrArg (fun z : ℤ => (z : ZMod 7)) hz
    push_cast at this
    exact this

/-- **The `j₉`-fibre over the CM value `−12288000` has the single
rational point `t = −3`** (PROVEN 2026-07-26): if a rational `t`
satisfies the denominator-free `X_0(9)` relation
`−12288000 · t⁹(t² + 9t + 27) = (t + 9)³(t³ + 243t² + 2187t + 6561)³`,
then `t = −3`.

This is the *sharpness* half of the level-`27` node: it is what makes
"`t` lies over `j(E)`" as strong as "`t` is **the** `X_0(9)`-parameter
of `E`", so that the level-`27` leaf below is not weakened by the way
its hypothesis is phrased. The proof clears denominators against
`t = t.num / t.den`, factors the resulting degree-`12` integral form as
`(N + 3D)(N² + 27D²)·Q(N, D)` — a `ring` identity, verified here — and
kills the two non-linear factors: `N² + 27D² > 0` because `D ≥ 1`, and
`Q(N, D) ≠ 0` by `x0NineFibre_int`. What survives is `N + 3D = 0`,
i.e. `t = −3`. -/
theorem x0Nine_fibre_over_CM (t : ℚ)
    (h : (-12288000 : ℚ) * (t ^ 9 * (t ^ 2 + 9 * t + 27))
      = (t + 9) ^ 3 * (t ^ 3 + 243 * t ^ 2 + 2187 * t + 6561) ^ 3) :
    t = -3 := by
  have hd0 : ((t.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr t.den_nz
  have hNq : ((t.num : ℚ)) = t * ((t.den : ℚ)) := (div_eq_iff hd0).mp (Rat.num_div_den t)
  have h7 : ¬ ((7 : ℤ) ∣ t.num ∧ (7 : ℤ) ∣ (t.den : ℤ)) := by
    rintro ⟨h1, h2⟩
    have h1' : 7 ∣ t.num.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr h1
    have h2' : 7 ∣ t.den := by exact_mod_cast h2
    have := Nat.dvd_gcd h1' h2'
    rw [t.reduced] at this
    omega
  have key : ((t.num + 3 * (t.den : ℤ)) * (t.num ^ 2 + 27 * (t.den : ℤ) ^ 2)
      * (t.num ^ 9 + 12288753 * t.num ^ 8 * (t.den : ℤ)
          + 73929348 * t.num ^ 7 * (t.den : ℤ) ^ 2
          - 199113228 * t.num ^ 6 * (t.den : ℤ) ^ 3
          - 1463588514 * t.num ^ 5 * (t.den : ℤ) ^ 4
          + 24020070318 * t.num ^ 4 * (t.den : ℤ) ^ 5
          + 255697522740 * t.num ^ 3 * (t.den : ℤ) ^ 6
          + 1129718145924 * t.num ^ 2 * (t.den : ℤ) ^ 7
          + 2541865828329 * t.num * (t.den : ℤ) ^ 8
          + 2541865828329 * (t.den : ℤ) ^ 9) : ℤ) = 0 := by
    have hq : (((t.num + 3 * (t.den : ℤ)) * (t.num ^ 2 + 27 * (t.den : ℤ) ^ 2)
        * (t.num ^ 9 + 12288753 * t.num ^ 8 * (t.den : ℤ)
            + 73929348 * t.num ^ 7 * (t.den : ℤ) ^ 2
            - 199113228 * t.num ^ 6 * (t.den : ℤ) ^ 3
            - 1463588514 * t.num ^ 5 * (t.den : ℤ) ^ 4
            + 24020070318 * t.num ^ 4 * (t.den : ℤ) ^ 5
            + 255697522740 * t.num ^ 3 * (t.den : ℤ) ^ 6
            + 1129718145924 * t.num ^ 2 * (t.den : ℤ) ^ 7
            + 2541865828329 * t.num * (t.den : ℤ) ^ 8
            + 2541865828329 * (t.den : ℤ) ^ 9) : ℤ) : ℚ) = 0 := by
      push_cast
      rw [hNq]
      linear_combination (-((t.den : ℚ) ^ 12)) * h
    exact_mod_cast hq
  rcases mul_eq_zero.mp key with hfac | hQ
  · rcases mul_eq_zero.mp hfac with hlin | hquad
    · have hnum : ((t.num : ℚ)) = -3 * ((t.den : ℚ)) := by
        have : ((t.num + 3 * (t.den : ℤ) : ℤ) : ℚ) = 0 := by exact_mod_cast hlin
        push_cast at this
        linarith
      rw [hNq] at hnum
      have : (t + 3) * ((t.den : ℚ)) = 0 := by linarith
      rcases mul_eq_zero.mp this with h1 | h1
      · linarith
      · exact absurd h1 hd0
    · exfalso
      have hdpos : (0 : ℤ) < (t.den : ℤ) := by exact_mod_cast Rat.den_pos t
      nlinarith [sq_nonneg t.num, mul_pos hdpos hdpos]
  · exact absurd hQ (x0NineFibre_int t.num (t.den : ℤ) h7)

/-!
##### The `3`-isogeny chain: from three `X_0(3)`-parameters to a point of `27a1`

(New 2026-07-26.) Everything in this section is PURE ARITHMETIC OVER `ℚ` —
no curves, no subgroups, no moduli — and all of it is PROVEN. It is the
Diophantine half of the level-`27` node, and it reduces the whole node to a
statement about `X_0(3)` alone (`exists_x0Three_chainParameters` below).

**The dictionary.** A curve with a `Gal(ℚ̄/ℚ)`-stable cyclic `27`-subgroup
`C` gives a chain of three rational `3`-isogenies

  `E = E₀ → E₁ = E₀/C[3] → E₂ = E₀/C[9] → E₃ = E₀/C`,

and each step `(E_{i}, C_{i+1}/C_i)` is a rational point of `X_0(3)`, i.e.
a value `uᵢ₊₁ ∈ ℚ` of the hauptmodul `t₃ = (η(τ)/η(3τ))¹²`, with

  `j(source) = (u+27)(u+243)³/u³`,  `j(quotient) = (u+27)(u+3)³/u`.

Matching the middle `j`-invariants gives, for consecutive parameters,
`(u+27)(u+3)³v³ = (v+27)(v+243)³u`, whose LHS−RHS **factors** (verified by
CAS, and here by `ring` inside every `linear_combination`) as

  `(uv − 729) · (u³v² + 36u²v² + 729u²v + 270uv² + 26244uv + 531441u − v³)`.

The first factor is the BACKTRACKING component `v = 729/u` — the Fricke
involution `w₃`, i.e. the second isogeny being the dual of the first — which
is exactly what cyclicity of the composite excludes. The second factor is
the residual `(3,3)` curve, which is `X_0(9)`: it is rational, with the
`X_0(9)` hauptmodul `s = (η(τ)/η(9τ))³` as parameter,

  `u = s³/(s²+9s+27)`,   `v = s(s²+9s+27)`,   and `u·v = s⁴`.

(Both parametrisations were found by fitting `q`-expansions of the
`η`-quotients to `O(q¹²⁰)` — untrusted searcher — and are PROVEN here as
polynomial identities.)

**What is new and what it buys.** The inverse of that parametrisation is an
explicit rational function (`exists_x0Nine_param_of_x0Three_pair`), and the
`X_0(27)` plane model that results,

  `s₁(s₁²+9s₁+27)(s₂²+9s₂+27) = s₂³`,

is birational to `27a1 : y² + y = x³ − 7` by the completely explicit map

  `x = (s₂+9)/(s₁+3)`,   `y = −s₂−5`,   inverse `s₁ = (4−3x−y)/x`,
  `s₂ = −y−5`,

which rests on the one-line identity `(s₂²+9s₂+27)(s₁+3)³ = (s₂+9)³`
(`exists_x0TwentySeven_point_of_planeModel`). So the ENTIRE passage from
level-`3` data to a rational point of `27a1` — previously assumed inside the
level-`27` moduli leaf — is now proven algebra.

**The one arithmetic obstruction, and how it is discharged.** Inverting the
parametrisation divides by `D = uv + 9v − 243u + 729`, and `D` vanishes at
base points. On the residual curve `D = 0` forces
`(v+243)²(v²−486v−19683)² = 0`; the quadratic factor has roots
`243 ± 162√3`, hence NO rational root (`x0Nine_denom_no_rat_root`, proven
from `Rat.reduced` plus the integer bound `280² < 78732 < 281²`), so the only
rational point with `D = 0` is `(u, v) = (−3, −243)` — where `uv = 729`, i.e.
exactly a backtracking point. **So non-backtracking is precisely what makes
the inversion legal**, which is a pleasant coincidence rather than a design
choice.

**Numerical anchor** (PARI/GP + Magma, untrusted searchers; every number
below is re-derived by `ring` in the proofs). The conductor-`27` isogeny
class has `j`-invariants `(0, −12288000, 0, −12288000)`; the unique cyclic
`27`-isogeny joins the two `j = −12288000` curves through TWO `j = 0` curves,
and the chain parameters are `(u₁, u₂, u₃) = (−3, −27, −243)`, with
`s₁ = −3`, `s₂ = −9` and the `27a1` point `(x, y) = (3, 4)`. Note
`u₁u₂ = 81 ≠ 729` and `u₂u₃ = 6561 ≠ 729`, as non-backtracking requires.
-/

/-- **`b² − 486b − 19683` has no rational root** (PROVEN): its roots are
`243 ± 162√3`. Proof: clearing denominators against `b = b.num/b.den` shows
`b.den ∣ b.num²`, so `b.den = 1` by `Rat.reduced`; then
`(b.num − 243)² = 78732`, which is impossible because `280² = 78400` and
`281² = 78961`. This is the arithmetic input that makes the `X_0(9)`
parametrisation invertible at every non-backtracking rational point. -/
lemma x0Nine_denom_no_rat_root (b : ℚ) (h : b ^ 2 - 486 * b - 19683 = 0) : False := by
  have hd0 : ((b.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr b.den_nz
  have hNq : ((b.num : ℚ)) = b * ((b.den : ℚ)) := (div_eq_iff hd0).mp (Rat.num_div_den b)
  have key : ((b.num : ℚ)) ^ 2 =
      486 * ((b.num : ℚ)) * ((b.den : ℚ)) + 19683 * ((b.den : ℚ)) ^ 2 := by
    rw [hNq]; linear_combination ((b.den : ℚ)) ^ 2 * h
  have keyZ : b.num ^ 2 = 486 * b.num * (b.den : ℤ) + 19683 * (b.den : ℤ) ^ 2 := by
    exact_mod_cast key
  have hdvd : (b.den : ℤ) ∣ b.num ^ 2 :=
    ⟨486 * b.num + 19683 * (b.den : ℤ), by linarith [keyZ]⟩
  have h2 : b.den ∣ b.num.natAbs ^ 2 := by
    have := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa [Int.natAbs_pow] using this
  have hden1 : b.den = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right 2 b.reduced.symm) h2
  rw [hden1] at keyZ
  push_cast at keyZ
  have hsq : (b.num - 243) ^ 2 = 78732 := by linarith [keyZ]
  have habs : |b.num - 243| ^ 2 = 78732 := by rw [sq_abs]; exact hsq
  have hm0 : (0 : ℤ) ≤ |b.num - 243| := abs_nonneg _
  rcases le_or_gt |b.num - 243| 280 with hle | hgt
  · nlinarith [habs, hm0, hle]
  · nlinarith [habs, hgt]

/-- **Away from backtracking the inverting denominator is nonzero** (PROVEN):
on the residual `X_0(9)` curve, `D = ab + 9b − 243a + 729 = 0` forces
`(b+243)²(b²−486b−19683)² = 0` (a polynomial identity, the pseudo-remainder of
the curve equation by `D` in `a`), hence `b = −243` and then `a = −3`, where
`ab = 729`. -/
lemma x0Nine_param_denom_ne_zero (a b : ℚ)
    (hG : a ^ 3 * b ^ 2 + 36 * a ^ 2 * b ^ 2 + 729 * a ^ 2 * b + 270 * a * b ^ 2
      + 26244 * a * b + 531441 * a = b ^ 3) (hnb : a * b ≠ 729) :
    a * b + 9 * b - 243 * a + 729 ≠ 0 := by
  intro hD
  have hfac : (b + 243) ^ 2 * (b ^ 2 - 486 * b - 19683) ^ 2 = 0 := by
    linear_combination
      ((b ^ 4 - 486 * b ^ 3 + 59049 * b ^ 2) * a ^ 2
        + (27 * b ^ 4 - 15309 * b ^ 3 + 1948617 * b ^ 2 + 43046721 * b) * a
        + 27 * b ^ 4 - 45927 * b ^ 3 + 11691702 * b ^ 2 + 1420541793 * b
        + 31381059609) * hD - (b - 243) ^ 3 * hG
  rcases mul_eq_zero.mp hfac with h1 | h1
  · have hb : b = -243 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
      linarith
    subst hb
    exact hnb (by linarith [hD])
  · exact x0Nine_denom_no_rat_root b (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1)

/-- **The `X_0(9)`-parameter of a non-backtracking pair of consecutive
`3`-isogenies** (PROVEN): the explicit rational inverse of the degree-`3`
parametrisation `a = s³/(s²+9s+27)`, `b = s(s²+9s+27)` of the residual
`(3,3)` curve, namely

  `s = (1458a + b(a²+18a+27)) / (ab + 9b − 243a + 729)`.

Both defining identities are `ring` identities modulo the curve equation
(cofactors `−(243a³+5103a²+6561a−19683)` and
`−(a³b+27a²b+1458a²+243ab+729b+39366)`), so the kernel checks the whole
inversion. -/
lemma exists_x0Nine_param_of_x0Three_pair (a b : ℚ)
    (hG : a ^ 3 * b ^ 2 + 36 * a ^ 2 * b ^ 2 + 729 * a ^ 2 * b + 270 * a * b ^ 2
      + 26244 * a * b + 531441 * a = b ^ 3) (hnb : a * b ≠ 729) :
    ∃ s : ℚ, a * (s ^ 2 + 9 * s + 27) = s ^ 3 ∧ b = s * (s ^ 2 + 9 * s + 27) := by
  have hDne : a * b + 9 * b - 243 * a + 729 ≠ 0 := x0Nine_param_denom_ne_zero a b hG hnb
  set D : ℚ := a * b + 9 * b - 243 * a + 729 with hDdef
  set N : ℚ := 1458 * a + b * (a ^ 2 + 18 * a + 27) with hNdef
  have e1 : a * (N ^ 2 + 9 * N * D + 27 * D ^ 2) * D = N ^ 3 := by
    rw [hNdef, hDdef]
    linear_combination (-(243 * a ^ 3 + 5103 * a ^ 2 + 6561 * a - 19683)) * hG
  have e2 : b * D ^ 3 = N * (N ^ 2 + 9 * N * D + 27 * D ^ 2) := by
    rw [hNdef, hDdef]
    linear_combination
      (-(a ^ 3 * b + 27 * a ^ 2 * b + 1458 * a ^ 2 + 243 * a * b + 729 * b + 39366)) * hG
  have expand : (N / D) ^ 2 + 9 * (N / D) + 27 = (N ^ 2 + 9 * N * D + 27 * D ^ 2) / D ^ 2 := by
    field_simp
  refine ⟨N / D, ?_, ?_⟩
  · rw [expand, div_pow, ← mul_div_assoc,
      div_eq_div_iff (pow_ne_zero 2 hDne) (pow_ne_zero 3 hDne)]
    linear_combination D ^ 2 * e1
  · rw [expand, div_mul_div_comm,
      eq_div_iff (mul_ne_zero hDne (pow_ne_zero 2 hDne))]
    linear_combination e2

/-- **The plane model of `X_0(27)` is birational to `27a1`** (PROVEN): from
`s₁(s₁²+9s₁+27)(s₂²+9s₂+27) = s₂³` — the two `X_0(9)`-parameters of the two
consecutive `9`-isogeny sub-chains, glued along their common middle
`X_0(3)`-parameter — one reads off a rational point of `y² + y = x³ − 7`
together with its image `s₁` under the degeneracy map `(x, y) ↦ (4−3x−y)/x`.

The whole content is the identity `(s₂²+9s₂+27)(s₁+3)³ = (s₂+9)³`, which is
the hypothesis plus `(s₁+3)³ = s₁(s₁²+9s₁+27) + 27`. Then `x = (s₂+9)/(s₁+3)`
and `y = −s₂−5`, with `x³ = s₂²+9s₂+27` and `y²+y = s₂²+9s₂+20 = x³−7`. The
base point `s₁ = −3` (which forces `s₂ = −9`) is exactly the CM point and is
handled by exhibiting `(x, y) = (3, 4)` directly. -/
lemma exists_x0TwentySeven_point_of_planeModel (s₁ s₂ : ℚ)
    (h : s₁ * (s₁ ^ 2 + 9 * s₁ + 27) * (s₂ ^ 2 + 9 * s₂ + 27) = s₂ ^ 3) :
    ∃ x y : ℚ, y ^ 2 + y = x ^ 3 - 7 ∧ s₁ * x = 4 - 3 * x - y := by
  have key : (s₂ ^ 2 + 9 * s₂ + 27) * (s₁ + 3) ^ 3 = (s₂ + 9) ^ 3 := by
    linear_combination h
  by_cases h3 : s₁ + 3 = 0
  · refine ⟨3, 4, by norm_num, ?_⟩
    have hs : s₁ = -3 := by linarith
    rw [hs]; norm_num
  · refine ⟨(s₂ + 9) / (s₁ + 3), -s₂ - 5, ?_, ?_⟩
    · rw [div_pow, ← sub_eq_zero]
      field_simp
      linear_combination key
    · field_simp
      ring

/-- **The `j`-relation transported from level `3` to level `9`** (PROVEN):
under `a(s²+9s+27) = s³` the `X_0(3)` `j`-map at `a` and the `X_0(9)` `j`-map
`j₉` at `s` agree. The mechanism is that `(s+9)³ = (s²+9s+27)(a+27)` and
`s³+243s²+2187s+6561 = (s²+9s+27)(a+243)`, so both sides differ by exactly
`(s²+9s+27)⁴`. -/
lemma j_relation_of_x0Three_param (J a s : ℚ)
    (ha : J * a ^ 3 = (a + 27) * (a + 243) ^ 3)
    (hs : a * (s ^ 2 + 9 * s + 27) = s ^ 3) :
    J * (s ^ 9 * (s ^ 2 + 9 * s + 27))
      = (s + 9) ^ 3 * (s ^ 3 + 243 * s ^ 2 + 2187 * s + 6561) ^ 3 := by
  have e1 : (s + 9) ^ 3 = (s ^ 2 + 9 * s + 27) * (a + 27) := by linear_combination -hs
  have e2 : s ^ 3 + 243 * s ^ 2 + 2187 * s + 6561 = (s ^ 2 + 9 * s + 27) * (a + 243) := by
    linear_combination -hs
  have e3 : s ^ 9 = a ^ 3 * (s ^ 2 + 9 * s + 27) ^ 3 := by
    linear_combination
      (-(s ^ 6 + s ^ 3 * a * (s ^ 2 + 9 * s + 27) + a ^ 2 * (s ^ 2 + 9 * s + 27) ^ 2)) * hs
  rw [e1, e2, e3]
  linear_combination (s ^ 2 + 9 * s + 27) ^ 4 * ha

/-- **The whole Diophantine half of the level-`27` node** (PROVEN): three
`X_0(3)`-parameters of a non-backtracking chain of three rational
`3`-isogenies, together with the `j`-value of the first curve, produce a
rational point of `27a1` lying over an `X_0(9)`-parameter of `E` with the
`j₉`-compatibility. Everything below `exists_x0Three_chainParameters` is this
lemma. -/
lemma x0TwentySeven_moduliPoint_of_chainParameters (J u₁ u₂ u₃ : ℚ)
    (hj : J * u₁ ^ 3 = (u₁ + 27) * (u₁ + 243) ^ 3)
    (hG12 : u₁ ^ 3 * u₂ ^ 2 + 36 * u₁ ^ 2 * u₂ ^ 2 + 729 * u₁ ^ 2 * u₂ + 270 * u₁ * u₂ ^ 2
      + 26244 * u₁ * u₂ + 531441 * u₁ = u₂ ^ 3)
    (hG23 : u₂ ^ 3 * u₃ ^ 2 + 36 * u₂ ^ 2 * u₃ ^ 2 + 729 * u₂ ^ 2 * u₃ + 270 * u₂ * u₃ ^ 2
      + 26244 * u₂ * u₃ + 531441 * u₂ = u₃ ^ 3)
    (hnb1 : u₁ * u₂ ≠ 729) (hnb2 : u₂ * u₃ ≠ 729) :
    ∃ x y s : ℚ, y ^ 2 + y = x ^ 3 - 7 ∧ s * x = 4 - 3 * x - y ∧
      J * (s ^ 9 * (s ^ 2 + 9 * s + 27))
        = (s + 9) ^ 3 * (s ^ 3 + 243 * s ^ 2 + 2187 * s + 6561) ^ 3 := by
  obtain ⟨s₁, hs₁a, hs₁b⟩ := exists_x0Nine_param_of_x0Three_pair u₁ u₂ hG12 hnb1
  obtain ⟨s₂, hs₂a, -⟩ := exists_x0Nine_param_of_x0Three_pair u₂ u₃ hG23 hnb2
  have hplane : s₁ * (s₁ ^ 2 + 9 * s₁ + 27) * (s₂ ^ 2 + 9 * s₂ + 27) = s₂ ^ 3 := by
    rw [← hs₁b]; exact hs₂a
  obtain ⟨x, y, hxy, hsx⟩ := exists_x0TwentySeven_point_of_planeModel s₁ s₂ hplane
  exact ⟨x, y, s₁, hxy, hsx, j_relation_of_x0Three_param J u₁ s₁ hj hs₁a⟩

end MazurLevel27

/-!
##### Level `3`: the `X_0(3)` universal family, and the chain glue (2026-07-26)

`exists_x0Three_chainParameters` is PROVEN below over TWO shallower leaves.
The cut separates, once and for all, the *arithmetic* of `X_0(3)` — which is
elementary and is proven here — from the *moduli* content, which is not.

**The dictionary, in Tate coordinates.** A pair `(E, C)` with `C` a
`Gal(ℚ̄/ℚ)`-stable subgroup of order `3` has `x(P) ∈ ℚ` for the two nonzero
`P ∈ C` (the pair `±P` is stable and `x(−P) = x(P)`), so after translating
`x(P)` to the origin and twisting quadratically — which does not move `j` —
the curve is `y² + a₁xy + a₃y = x³` with `C = ⟨(0,0)⟩`. There

  `b₂ = a₁²`, `b₄ = a₁a₃`, `b₆ = a₃²`, `b₈ = 0`,
  `c₄ = a₁(a₁³ − 24a₃)`, `Δ = a₃³(a₁³ − 27a₃)`,

so `a₃ ≠ 0` and `a₁³ − 27a₃ ≠ 0` are exactly nonsingularity, and

  `j(E) = a₁³(a₁³ − 24a₃)³ / (a₃³(a₁³ − 27a₃))`.

Vélu's formulas at the kernel `{0, (0,0), (0,−a₃)}` give `t = b₄ = a₁a₃` and
`w = a₃²` (both terms are `±`-invariant and equal at the two nonzero points),
hence `E/C : y² + a₁xy + a₃y = x³ − 5a₁a₃x − (a₁³a₃ + 7a₃²)` with
`c₄' = a₁(a₁³ + 216a₃)` and `Δ' = a₃(a₁³ − 27a₃)³`, so

  `j(E/C) = a₁³(a₁³ + 216a₃)³ / (a₃(a₁³ − 27a₃)³)`.

With the `X_0(3)` hauptmodul `t₃ = (η(τ)/η(3τ))¹²` the parameter of `(E, C)`
is `u = 729a₃/(a₁³ − 27a₃)` — always defined and nonzero — and the two
displayed `j`-values become the two classical `j`-maps

  `j(source) = (u+27)(u+243)³/u³`,   `j(quotient) = (u+27)(u+3)³/u`,

which are exchanged by the Fricke involution `w₃ : u ↦ 729/u`. That last
translation is `X0Three.param_of_tateInvariants`, PROVEN below by clearing
`(a₁³ − 27a₃)⁴` and one `linear_combination`.

**Numerical anchor.** For the class `27a` the chain is
`j = (−12288000, 0, 0, −12288000)` with `(u₁, u₂, u₃) = (−3, −27, −243)`;
`u₁ = −3` corresponds to `h := a₁³/a₃ = −216`, and indeed
`h(h−24)³/(h−27) = −12288000` and `h(h+216)³/(h−27)³ = 0`.
-/

namespace X0Three

/-- **From Tate invariants to the `X_0(3)` hauptmodul parameter** (PROVEN):
if `J`, `J'` are the `j`-invariants of `y² + a₁xy + a₃y = x³` and of its
quotient by `⟨(0,0)⟩`, written denominator-free against
`Δ = a₃³(a₁³ − 27a₃)` and `Δ' = a₃(a₁³ − 27a₃)³`, then `u = 729a₃/(a₁³−27a₃)`
is a nonzero rational satisfying the two `X_0(3)` `j`-map relations.

The whole proof is the three linear identities
`(u+27)(a₁³−27a₃) = 27a₁³`, `(u+243)(a₁³−27a₃) = 243(a₁³−24a₃)` and
`(u+3)(a₁³−27a₃) = 3(a₁³+216a₃)` together with `u³(a₁³−27a₃)³ = 729³a₃³`;
cancelling `(a₁³−27a₃)⁴` turns each goal into `729³ ·` resp. `729 ·` the
hypothesis. -/
lemma param_of_tateInvariants (J J' a₁ a₃ : ℚ) (h3 : a₃ ≠ 0)
    (hD : a₁ ^ 3 - 27 * a₃ ≠ 0)
    (hJ : J * (a₃ ^ 3 * (a₁ ^ 3 - 27 * a₃)) = a₁ ^ 3 * (a₁ ^ 3 - 24 * a₃) ^ 3)
    (hJ' : J' * (a₃ * (a₁ ^ 3 - 27 * a₃) ^ 3) = a₁ ^ 3 * (a₁ ^ 3 + 216 * a₃) ^ 3) :
    ∃ u : ℚ, u ≠ 0 ∧ J * u ^ 3 = (u + 27) * (u + 243) ^ 3 ∧
      J' * u = (u + 27) * (u + 3) ^ 3 := by
  obtain ⟨u, hu⟩ : ∃ u : ℚ, u * (a₁ ^ 3 - 27 * a₃) = 729 * a₃ :=
    ⟨729 * a₃ / (a₁ ^ 3 - 27 * a₃), div_mul_cancel₀ _ hD⟩
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact h3 (by linarith [hu])
  have hA : u ^ 3 * (a₁ ^ 3 - 27 * a₃) ^ 3 = 729 ^ 3 * a₃ ^ 3 := by
    rw [← mul_pow, hu]; ring
  have hB : (u + 27) * (a₁ ^ 3 - 27 * a₃) = 27 * a₁ ^ 3 := by linear_combination hu
  have hC : (u + 243) * (a₁ ^ 3 - 27 * a₃) = 243 * (a₁ ^ 3 - 24 * a₃) := by
    linear_combination hu
  have hE : (u + 3) * (a₁ ^ 3 - 27 * a₃) = 3 * (a₁ ^ 3 + 216 * a₃) := by
    linear_combination hu
  refine ⟨u, hu0, ?_, ?_⟩
  · refine mul_right_cancel₀ (pow_ne_zero 4 hD) ?_
    have hL : J * u ^ 3 * (a₁ ^ 3 - 27 * a₃) ^ 4
        = J * (u ^ 3 * (a₁ ^ 3 - 27 * a₃) ^ 3) * (a₁ ^ 3 - 27 * a₃) := by ring
    have hR : (u + 27) * (u + 243) ^ 3 * (a₁ ^ 3 - 27 * a₃) ^ 4
        = ((u + 27) * (a₁ ^ 3 - 27 * a₃)) * ((u + 243) * (a₁ ^ 3 - 27 * a₃)) ^ 3 := by
      ring
    rw [hL, hR, hA, hB, hC]
    linear_combination (387420489 : ℚ) * hJ
  · refine mul_right_cancel₀ (pow_ne_zero 4 hD) ?_
    have hL : J' * u * (a₁ ^ 3 - 27 * a₃) ^ 4
        = J' * (u * (a₁ ^ 3 - 27 * a₃)) * (a₁ ^ 3 - 27 * a₃) ^ 3 := by ring
    have hR : (u + 27) * (u + 3) ^ 3 * (a₁ ^ 3 - 27 * a₃) ^ 4
        = ((u + 27) * (a₁ ^ 3 - 27 * a₃)) * ((u + 3) * (a₁ ^ 3 - 27 * a₃)) ^ 3 := by
      ring
    rw [hL, hR, hu, hB, hE]
    linear_combination (729 : ℚ) * hJ'

/-- **The residual factor of the `j`-matching relation** (PROVEN): if the
middle curve of two consecutive `3`-isogenies has `X_0(3)`-parameter `u` as a
quotient and `v` as a source, then eliminating its `j` gives
`(u+27)(u+3)³v³ = (v+27)(v+243)³u`, whose two sides differ by

  `(uv − 729) · (u³v² + 36u²v² + 729u²v + 270uv² + 26244uv + 531441u − v³)`.

The first factor is the BACKTRACKING component `v = 729/u` — the Fricke
involution `w₃`, i.e. the second isogeny being the dual of the first — so once
non-backtracking `uv ≠ 729` is known the residual `(3,3)` curve equation holds.
That residual curve is `X_0(9)`; everything downstream of it is proven in
`MazurLevel27` above. -/
lemma residual_of_matching (J u v : ℚ)
    (h1 : J * u = (u + 27) * (u + 3) ^ 3)
    (h2 : J * v ^ 3 = (v + 27) * (v + 243) ^ 3)
    (hnb : u * v ≠ 729) :
    u ^ 3 * v ^ 2 + 36 * u ^ 2 * v ^ 2 + 729 * u ^ 2 * v + 270 * u * v ^ 2
      + 26244 * u * v + 531441 * u = v ^ 3 := by
  have hfac : (u * v - 729) *
      (u ^ 3 * v ^ 2 + 36 * u ^ 2 * v ^ 2 + 729 * u ^ 2 * v + 270 * u * v ^ 2
        + 26244 * u * v + 531441 * u - v ^ 3) = 0 := by
    linear_combination (-(v ^ 3)) * h1 + u * h2
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (by linarith : u * v = 729) hnb
  · linarith

section Groups

variable {G H I : Type*} [AddCommGroup G] [AddCommGroup H] [AddCommGroup I]

/-- **A nonzero element killed by a prime has that prime as its order**
(PROVEN): elementary, and used twice below to certify that each kernel of the
`3`-isogeny chain really has order `3`. -/
lemma addOrderOf_eq_of_prime {A : Type*} [AddGroup A] {p : ℕ} (hp : p.Prime) (x : A)
    (h0 : x ≠ 0) (hpx : p • x = 0) : addOrderOf x = p := by
  rcases (Nat.dvd_prime hp).mp (addOrderOf_dvd_of_nsmul_eq_zero hpx) with h | h
  · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h) h0
  · exact h

/-- **Stability of a cyclic subgroup pushes forward along an equivariant
homomorphism** (PROVEN): if `⟨x⟩` is stable under a family of additive
operators `aG` and `φ` intertwines `aG` with `aH`, then `⟨φ x⟩` is stable
under `aH`. This is the abstract form of "the image of a rational subgroup
under a rational isogeny is rational", and it is what carries Galois
stability along the `3`-isogeny chain. -/
lemma stable_map {Γ : Type*} (aG : Γ → G →+ G) (aH : Γ → H →+ H) (φ : G →+ H)
    (hgal : ∀ (σ : Γ) (x : G), φ (aG σ x) = aH σ (φ x)) (x : G)
    (hst : ∀ σ : Γ, ∀ y ∈ AddSubgroup.zmultiples x,
      aG σ y ∈ AddSubgroup.zmultiples x) :
    ∀ σ : Γ, ∀ y ∈ AddSubgroup.zmultiples (φ x),
      aH σ y ∈ AddSubgroup.zmultiples (φ x) := by
  intro σ y hy
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp
    (hst σ x (AddSubgroup.mem_zmultiples x))
  have key : aH σ (k • φ x) = (k * m) • φ x := by
    rw [map_zsmul, ← hgal σ x, ← hm, map_zsmul, smul_smul]
  rw [key]
  exact AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples _) _

/-- **The second kernel of the chain is nonzero** (PROVEN): if `g` has order
`27` and `φ` has kernel exactly `⟨9g⟩`, then `φ(3g) ≠ 0`. Otherwise
`3g = k·9g` in `⟨g⟩ ≅ ℤ/27`, i.e. `27 ∣ 9k − 3`, which fails already
modulo `9`. -/
lemma map_three_ne_zero (φ : G →+ H) (g : G) (hg : addOrderOf g = 27)
    (hker : ∀ x, φ x = 0 ↔ x ∈ AddSubgroup.zmultiples ((9 : ℕ) • g)) :
    φ ((3 : ℕ) • g) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp ((hker _).mp h)
  have hz : ((9 * k - 3 : ℤ)) • g = 0 := by
    have h9 : (9 * k : ℤ) • g = (3 : ℤ) • g := by
      calc (9 * k : ℤ) • g = k • ((9 : ℤ) • g) := by rw [smul_smul, mul_comm]
        _ = k • ((9 : ℕ) • g) := by norm_cast
        _ = (3 : ℕ) • g := hk
        _ = (3 : ℤ) • g := by norm_cast
    rw [sub_smul, h9, sub_self]
  have hdvd : ((27 : ℤ)) ∣ (9 * k - 3) := by
    have := addOrderOf_dvd_iff_zsmul_eq_zero.mpr hz
    rw [hg] at this
    exact_mod_cast this
  omega

/-- **The third kernel of the chain is nonzero** (PROVEN): with `g` of order
`27`, `ker φ = ⟨9g⟩` and `ker ψ = ⟨φ(3g)⟩`, one has `ψ(φ g) ≠ 0`. Otherwise
`φ g = k·φ(3g)`, so `φ((3k − 1)g) = 0`, so `(3k − 1)g ∈ ⟨9g⟩` and
`27 ∣ 9m − 3k + 1`, impossible modulo `3`. This is exactly the CYCLICITY of
`⟨g⟩` being used: it is what makes the three quotients a chain rather than a
product. -/
lemma map_map_ne_zero (φ : G →+ H) (ψ : H →+ I) (g : G) (hg : addOrderOf g = 27)
    (hkerφ : ∀ x, φ x = 0 ↔ x ∈ AddSubgroup.zmultiples ((9 : ℕ) • g))
    (hkerψ : ∀ y, ψ y = 0 ↔ y ∈ AddSubgroup.zmultiples (φ ((3 : ℕ) • g))) :
    ψ (φ g) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp ((hkerψ _).mp h)
  have h3 : φ ((3 : ℕ) • g) = (3 : ℤ) • φ g := by rw [map_nsmul]; norm_cast
  rw [h3, smul_smul] at hk
  have hφ : φ (((k * 3 - 1 : ℤ)) • g) = 0 := by
    rw [map_zsmul, sub_smul, one_smul, hk, sub_self]
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp ((hkerφ _).mp hφ)
  have hz : ((9 * m - (k * 3 - 1) : ℤ)) • g = 0 := by
    have h9 : (9 * m : ℤ) • g = ((k * 3 - 1 : ℤ)) • g := by
      calc (9 * m : ℤ) • g = m • ((9 : ℤ) • g) := by rw [smul_smul, mul_comm]
        _ = m • ((9 : ℕ) • g) := by norm_cast
        _ = ((k * 3 - 1 : ℤ)) • g := hm
    rw [sub_smul, h9, sub_self]
  have hdvd : ((27 : ℤ)) ∣ (9 * m - (k * 3 - 1)) := by
    have := addOrderOf_dvd_iff_zsmul_eq_zero.mpr hz
    rw [hg] at this
    exact_mod_cast this
  omega

end Groups

end X0Three

/-- **`X_0(3)`: the Tate invariants of a rational `3`-isogeny** (sorry leaf,
cut 2026-07-26 out of `exists_x0Three_chainParameters`). For an elliptic curve
`E/ℚ` and a `Gal(ℚ̄/ℚ)`-stable subgroup `⟨P⟩` of order `3` in `E(ℚ̄)`, there
are `a₁, a₃ ∈ ℚ` and a quotient isogeny `φ : E(ℚ̄) → E'(ℚ̄)` over `ℚ` with
kernel exactly `⟨P⟩` such that

* `a₃ ≠ 0` and `a₁³ − 27a₃ ≠ 0` (i.e. `Δ = a₃³(a₁³ − 27a₃) ≠ 0`);
* `j(E) · a₃³(a₁³ − 27a₃) = a₁³(a₁³ − 24a₃)³`;
* `j(E/⟨P⟩) · a₃(a₁³ − 27a₃)³ = a₁³(a₁³ + 216a₃)³`.

This is the `X_0(3)` universal family, stated denominator-free. See the
section note above for the derivation of both formulas; they are elementary
algebra ONCE the normal form is available, and the normal form is the content.

**Route.** Three steps, in this order.

1. *The `x`-coordinate is rational.* `⟨P⟩ = {0, P, −P}` is stable and
   `x(−P) = x(P)`, so `x(P)` is fixed by `Gal(ℚ̄/ℚ)`, hence lies in `ℚ`
   (`WeierstrassCurve.exists_point_eq_baseChange_of_fixed` is the analogous
   descent already used for the `2`-isogeny leaf; here only the coordinate
   descends, not the point).
2. *The normal form.* Translate `x(P)` to `0`; then `x(2P) = x(−P) = 0`
   forces `b₈ = 0`, and after the `y`-shift and tangent normalisation
   available over `ℚ(y(P))` the model is `y² + a₁xy + a₃y = x³` with
   `P = (0, 0)`. `y(P)` generates a quadratic extension in general, so what
   descends is the QUADRATIC TWIST class: twisting does not move `j`, and
   `(E/C)^d = E^d/C^d`, so BOTH displayed identities are twist-invariant and
   may be verified on the untwisted model.
   `WeierstrassCurve.exists_tateNormalForm` (PROVEN above) is the order-`≥ 4`
   analogue and is the pattern to copy;
   `WeierstrassCurve.three_nsmul_origin_eq_zero` (PROVEN above) is the
   converse direction already available.
3. *The quotient.* `WeierstrassCurve.exists_velu_quotient_isogeny`
   (`Fermat/FLT/EllipticCurve/Velu.lean`, and NOT the `MazurTorsion`
   re-packaging `exists_quotient_isogeny_of_prime_card`, which is declared
   far BELOW this point and so is unavailable here) already produces `φ`, and
   its quotient curve is literally `E.veluModel t w`. At the kernel
   `{0, (0,0), (0,−a₃)}` both Vélu terms are `±`-invariant and equal at the
   two nonzero points, so `t = b₄ = a₁a₃` and `w = a₃²`, giving
   `E/C : y² + a₁xy + a₃y = x³ − 5a₁a₃x − (a₁³a₃ + 7a₃²)`,
   `c₄' = a₁(a₁³ + 216a₃)`, `Δ' = a₃(a₁³ − 27a₃)³` — three `ring` identities.
   What `exists_velu_quotient_isogeny` does NOT currently expose is the
   identity of `E'` with `E.veluModel t w`; strengthening its conclusion to
   name the model is the cheapest way to get this leaf.

**Faithfulness.** The statement is an existential over `(a₁, a₃, E', φ)`
JOINTLY, so it does not assert anything about an arbitrary group homomorphism
with kernel `⟨P⟩` — it asserts that the Vélu quotient exists and has the
stated `j`. Non-vacuous: for `E` in the class `27a` with `j = −12288000` and
`u₁ = −3` the invariants satisfy `a₁³ = −216a₃`, and both identities hold with
`j(E/C) = 0`. -/
theorem WeierstrassCurve.exists_tateInvariants_of_stableThreeSubgroup
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄(AlgebraicClosure ℚ)).Point) (hP : addOrderOf P = 3)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples P,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples P) :
    ∃ (a₁ a₃ : ℚ) (E' : WeierstrassCurve ℚ) (_hE' : E'.IsElliptic)
      (φ : (E⁄(AlgebraicClosure ℚ)).Point →+ (E'⁄(AlgebraicClosure ℚ)).Point),
      (∀ (σ : Field.absoluteGaloisGroup ℚ)
        (Pt : (E⁄(AlgebraicClosure ℚ)).Point),
        φ (Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom Pt) =
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom (φ Pt)) ∧
      (∀ Pt : (E⁄(AlgebraicClosure ℚ)).Point,
        φ Pt = 0 ↔ Pt ∈ AddSubgroup.zmultiples P) ∧
      a₃ ≠ 0 ∧ a₁ ^ 3 - 27 * a₃ ≠ 0 ∧
      E.j * (a₃ ^ 3 * (a₁ ^ 3 - 27 * a₃)) = a₁ ^ 3 * (a₁ ^ 3 - 24 * a₃) ^ 3 ∧
      E'.j * (a₃ * (a₁ ^ 3 - 27 * a₃) ^ 3) = a₁ ^ 3 * (a₁ ^ 3 + 216 * a₃) ^ 3 :=
  sorry

/-- **`X_0(3)`: the hauptmodul parameter of a rational `3`-isogeny** (PROVEN
2026-07-26 over the single leaf
`exists_tateInvariants_of_stableThreeSubgroup`): a `Gal(ℚ̄/ℚ)`-stable subgroup
`⟨P⟩` of order `3` in `E(ℚ̄)` has an `X_0(3)` hauptmodul value `u ∈ ℚ∖{0}`
together with the quotient isogeny, and

* `j(E) · u³ = (u+27)(u+243)³` — the `j`-map of `X_0(3)` at the source;
* `j(E/⟨P⟩) · u = (u+27)(u+3)³` — the `j`-map at the quotient.

The proof is `X0Three.param_of_tateInvariants` applied to the Tate invariants:
`u = 729a₃/(a₁³ − 27a₃)`. Note the two `j`-maps are exchanged by the Fricke
involution `u ↦ 729/u`, which is why the second one appears with `u` rather
than `u³`. -/
theorem WeierstrassCurve.exists_x0Three_param_of_stableThreeSubgroup
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄(AlgebraicClosure ℚ)).Point) (hP : addOrderOf P = 3)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples P,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples P) :
    ∃ (u : ℚ) (E' : WeierstrassCurve ℚ) (_hE' : E'.IsElliptic)
      (φ : (E⁄(AlgebraicClosure ℚ)).Point →+ (E'⁄(AlgebraicClosure ℚ)).Point),
      (∀ (σ : Field.absoluteGaloisGroup ℚ)
        (Pt : (E⁄(AlgebraicClosure ℚ)).Point),
        φ (Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom Pt) =
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom (φ Pt)) ∧
      (∀ Pt : (E⁄(AlgebraicClosure ℚ)).Point,
        φ Pt = 0 ↔ Pt ∈ AddSubgroup.zmultiples P) ∧
      u ≠ 0 ∧
      E.j * u ^ 3 = (u + 27) * (u + 243) ^ 3 ∧
      E'.j * u = (u + 27) * (u + 3) ^ 3 := by
  obtain ⟨a₁, a₃, E', hE', φ, hgal, hker, ha3, hDne, hJ, hJ'⟩ :=
    E.exists_tateInvariants_of_stableThreeSubgroup P hP hstable
  haveI := hE'
  obtain ⟨u, hu0, h1, h2⟩ :=
    X0Three.param_of_tateInvariants E.j E'.j a₁ a₃ ha3 hDne hJ hJ'
  exact ⟨u, E', hE', φ, hgal, hker, hu0, h1, h2⟩

/-- **Non-backtracking along a cyclic `9`-isogeny** (sorry leaf, cut
2026-07-26 out of `exists_x0Three_chainParameters`): for a chain
`E → E' → E''` of two rational `3`-isogenies whose composite has CYCLIC
kernel `⟨h⟩` of order `9` (`9h = 0`, `3h ≠ 0`, `ker φ = ⟨3h⟩`,
`ker ψ = ⟨φ h⟩`, everything `Gal(ℚ̄/ℚ)`-stable and equivariant), the two
`X_0(3)` hauptmodul parameters satisfy `uv ≠ 729`.

**Why this is not free, and why skipping it states a FALSE leaf.** `uv = 729`
is the Fricke locus `v = w₃(u)`: it says `(E', ker ψ)` and
`(E', φ(E[3])) = (E', ker φ̂)` have the SAME `X_0(3)`-parameter, i.e. the
second isogeny is the dual of the first, i.e. the composite kernel is `E[3]`
rather than cyclic. So this IS the cyclicity hypothesis, and it must be paid
for. Concretely, `uv = 729` forces `j(E'') = j(E)`: substituting `v = 729/u`
into `j(E'')v = (v+27)(v+3)³` returns `(u+27)(u+243)³/u³`.

**Route.** Two ingredients, and the second is where the real work is.

1. *The subgroups differ.* `ker ψ = ⟨φ h⟩` and `φ(E[3]) = ⟨φ(3h)⟩` are
   distinct, because `φ h ∈ ⟨φ(3h)⟩` would give `(3k−1)h ∈ ker φ = ⟨3h⟩`,
   i.e. `9 ∣ 3m − 3k + 1`, impossible modulo `3`. (This is
   `X0Three.map_map_ne_zero` one level down and is already proven.)
2. *Distinct stable `3`-subgroups have distinct parameters.* For
   `Aut(E') = ±1` the `X_0(3)`-parameter separates subgroups outright. The
   two exceptional `j` must BOTH be handled, because the real chain DOES pass
   through `j = 0`:
   * `j = 1728` cannot occur at all: for `y² = x³ + ax` the `3`-division
     polynomial is `3x⁴ + 6ax² − a²`, with `x² = a(−3 ± 2√3)/3`, so no
     `j = 1728` curve over `ℚ` has a rational `3`-isogeny.
   * `j = 0` DOES occur (the middle two curves of the class `27a`). There
     `Aut = μ₆` and `ζ₃` permutes the three non-canonical `3`-subgroups
     cyclically, fixing only `ker(√−3)`. If two of the three were
     Galois-stable then all four `3`-subgroups would be, so the mod-`3`
     representation would be SCALAR, its determinant — the mod-`3` cyclotomic
     character cutting out `ℚ(ζ₃) ≠ ℚ` — would be a square, hence trivial.
     Contradiction. So at most one non-canonical subgroup is stable, and the
     parameter does separate the stable ones.

**FAITHFULNESS AUDIT.** The statement is TRUE but is very slightly STRONGER
than the geometric non-backtracking, and the gap is worth recording because it
is where a future prover will get stuck.

`u` and `v` are pinned here only by their `j`-relations, not by a normal form.
The map `u ↦ (j_src(u), j_quot(u))` from `X_0(3)` to `X(1) × X(1)` fails to be
injective exactly when `E'` admits two `3`-subgroups in different `Aut`-orbits
with isomorphic quotients — which, composing one isogeny with the dual of the
other, produces a PRIMITIVE endomorphism of degree `9`, hence complex
multiplication by an order in which `3` splits or is non-maximal. Among the
thirteen class-number-one discriminants only `−8` and `−11` split at `3`, and
neither curve carries a rational cyclic `9`-isogeny (complex conjugation swaps
`𝔭` and `𝔭̄`, hence swaps `E[𝔭²]` and `E[𝔭̄²]`); the two CM `j`-invariants
that DO admit one, `0` (disc `−3`) and `−12288000` (disc `−27`), have no
primitive norm-`9` element at all — every solution of `a² − ab + b² = 9`
resp. `a² − 3ab + 9b² = 9` is divisible by `3`. So under the hypotheses of
this leaf the extra strength is vacuous. A prover who finds the gap
obstructive should thread the Tate invariants of
`exists_tateInvariants_of_stableThreeSubgroup` through instead of the bare
`j`-relations; that is a cut-level repair, not a refutation.

Numerical anchor (Magma `IsogenousCurves`, PARI/GP `ellisomat` — untrusted
searchers): for the class `27a`, `(u₁, u₂, u₃) = (−3, −27, −243)` with
`u₁u₂ = 81` and `u₂u₃ = 6561`, both `≠ 729`. -/
theorem WeierstrassCurve.x0Three_param_mul_ne_729
    (E E' E'' : WeierstrassCurve ℚ) [E.IsElliptic] [E'.IsElliptic] [E''.IsElliptic]
    (φ : (E⁄(AlgebraicClosure ℚ)).Point →+ (E'⁄(AlgebraicClosure ℚ)).Point)
    (ψ : (E'⁄(AlgebraicClosure ℚ)).Point →+ (E''⁄(AlgebraicClosure ℚ)).Point)
    (hφgal : ∀ (σ : Field.absoluteGaloisGroup ℚ)
        (Pt : (E⁄(AlgebraicClosure ℚ)).Point),
        φ (Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom Pt) =
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom (φ Pt))
    (hψgal : ∀ (σ : Field.absoluteGaloisGroup ℚ)
        (Pt : (E'⁄(AlgebraicClosure ℚ)).Point),
        ψ (Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom Pt) =
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom (ψ Pt))
    (h : (E⁄(AlgebraicClosure ℚ)).Point)
    (h9 : (9 : ℕ) • h = 0) (h3 : (3 : ℕ) • h ≠ 0)
    (hhstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples h,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples h)
    (hφker : ∀ Pt : (E⁄(AlgebraicClosure ℚ)).Point,
      φ Pt = 0 ↔ Pt ∈ AddSubgroup.zmultiples ((3 : ℕ) • h))
    (hψker : ∀ Pt : (E'⁄(AlgebraicClosure ℚ)).Point,
      ψ Pt = 0 ↔ Pt ∈ AddSubgroup.zmultiples (φ h))
    (u v : ℚ) (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hju : E.j * u ^ 3 = (u + 27) * (u + 243) ^ 3)
    (hju' : E'.j * u = (u + 27) * (u + 3) ^ 3)
    (hjv : E'.j * v ^ 3 = (v + 27) * (v + 243) ^ 3)
    (hjv' : E''.j * v = (v + 27) * (v + 3) ^ 3) :
    u * v ≠ 729 :=
  sorry

/-- **`X_0(3)`: the three hauptmodul parameters of the `3`-isogeny chain of a
rational cyclic `27`-subgroup** (PROVEN 2026-07-26 over the two level-`3`
leaves `exists_tateInvariants_of_stableThreeSubgroup` and
`x0Three_param_mul_ne_729`; cut 2026-07-26 out of
`exists_x0TwentySeven_moduliPoint`): if `E` carries a `Gal(ℚ̄/ℚ)`-stable
cyclic subgroup `C = ⟨g⟩` of order `27`, then the three consecutive rational
`3`-isogenies

  `E → E/C[3] → E/C[9] → E/C`

have `X_0(3)`-hauptmodul parameters `u₁, u₂, u₃ ∈ ℚ` — values of
`t₃ = (η(τ)/η(3τ))¹²` — satisfying

* `j(E) · u₁³ = (u₁+27)(u₁+243)³` — the `j`-map of `X_0(3)` at the first step;
* the two consecutive-`j` matching relations, in the form of the RESIDUAL
  factor after the backtracking component has been divided out;
* `u₁u₂ ≠ 729` and `u₂u₃ ≠ 729` — non-backtracking: the second isogeny of
  each consecutive pair is not the dual of the first, which is exactly
  CYCLICITY of the composite `9`-isogeny.

**This is a statement about `X_0(3)` ONLY.** No modular curve of level `9` or
`27` occurs in it, and no Jacobian: `X_0(3)` is `P¹` and its universal family
is elementary (a curve with a rational `3`-isogeny is, up to quadratic twist —
which does not move `j` — a Tate normal form `y² + a₁xy + a₃y = x³`, whence
`j = h(h−24)³/(h−27)` with `h = a₁³/a₃`, i.e. `j·u³ = (u+27)(u+243)³` after
`u = 729/(h − 27)`; the quotient's `j` is then a Vélu computation on that
explicit model). Everything of level `9` and `27` — the `X_0(9)` hauptmodul,
the plane model of `X_0(27)`, its birational identification with `27a1`, and
the Diophantine finish — is PROVEN above and below.

**The proof here is ALL GLUE — no moduli content is left in it.** Divisor
descent (`exists_stable_zmultiples_of_dvd` / `stable_zmultiples_nsmul`, both
proven above) gives the stable subgroups `⟨9g⟩ ⊂ ⟨3g⟩ ⊂ ⟨g⟩`. Three
applications of `exists_x0Three_param_of_stableThreeSubgroup` build the chain

  `E --φ₁--> E₁ --φ₂--> E₂ --φ₃--> E₃`,   `ker φ₁ = ⟨9g⟩`,
  `ker φ₂ = ⟨φ₁(3g)⟩`,   `ker φ₃ = ⟨φ₂(φ₁ g)⟩`,

each kernel having order exactly `3` by `X0Three.map_three_ne_zero` and
`X0Three.map_map_ne_zero` (this is where CYCLICITY of `⟨g⟩` enters — the two
lemmas are congruences modulo `9` resp. `3` inside `ℤ/27`) and being stable by
`X0Three.stable_map`. Each application returns BOTH `j`-maps, so each middle
curve is described twice: `j(E₁)u₁ = (u₁+27)(u₁+3)³` from step `1` and
`j(E₁)u₂³ = (u₂+27)(u₂+243)³` from step `2`. Eliminating `j(E₁)` gives the
matching relation, whose two sides differ by `(u₁u₂ − 729)` times the residual
`X_0(9)` polynomial (`X0Three.residual_of_matching`); non-backtracking
(`x0Three_param_mul_ne_729`) kills the first factor. Identically for `u₂, u₃`
with `j(E₂)`.

**Faithfulness.** The statement is satisfied by the unique curve it can
describe: `j(E) = −12288000` with `(u₁, u₂, u₃) = (−3, −27, −243)`, giving
`u₁u₂ = 81` and `u₂u₃ = 6561`. Checked numerically against `ellisomat` of the
class `27a` (PARI/GP) and `IsogenousCurves` (Magma). -/
theorem WeierstrassCurve.exists_x0Three_chainParameters
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) (hg : addOrderOf g = 27)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    ∃ u₁ u₂ u₃ : ℚ,
      E.j * u₁ ^ 3 = (u₁ + 27) * (u₁ + 243) ^ 3 ∧
      u₁ ^ 3 * u₂ ^ 2 + 36 * u₁ ^ 2 * u₂ ^ 2 + 729 * u₁ ^ 2 * u₂ + 270 * u₁ * u₂ ^ 2
        + 26244 * u₁ * u₂ + 531441 * u₁ = u₂ ^ 3 ∧
      u₂ ^ 3 * u₃ ^ 2 + 36 * u₂ ^ 2 * u₃ ^ 2 + 729 * u₂ ^ 2 * u₃ + 270 * u₂ * u₃ ^ 2
        + 26244 * u₂ * u₃ + 531441 * u₂ = u₃ ^ 3 ∧
      u₁ * u₂ ≠ 729 ∧ u₂ * u₃ ≠ 729 := by
  classical
  -- divisor descent inside `⟨g⟩ ≅ ℤ/27`
  have hst9 := E.stable_zmultiples_nsmul g 9 hstable
  have hst3 := E.stable_zmultiples_nsmul g 3 hstable
  have hord9 : addOrderOf ((9 : ℕ) • g) = 3 := by
    rw [addOrderOf_nsmul' g (by norm_num), hg]; norm_num
  have h33 : ((3 : ℕ) • ((3 : ℕ) • g)) = (9 : ℕ) • g := by rw [smul_smul]; norm_num
  have h39 : ((9 : ℕ) • ((3 : ℕ) • g)) = (27 : ℕ) • g := by rw [smul_smul]; norm_num
  have h9ne : (9 : ℕ) • g ≠ 0 := by
    intro hc
    simp [hc] at hord9
  -- STEP 1 : the isogeny with kernel `⟨9g⟩`
  obtain ⟨u₁, E₁, hE₁, φ₁, hφ₁gal, hφ₁ker, hu₁0, hj1, hj1'⟩ :=
    E.exists_x0Three_param_of_stableThreeSubgroup ((9 : ℕ) • g) hord9 hst9
  haveI := hE₁
  have hg₁ne : φ₁ ((3 : ℕ) • g) ≠ 0 := X0Three.map_three_ne_zero φ₁ g hg hφ₁ker
  have hg₁3 : (3 : ℕ) • φ₁ ((3 : ℕ) • g) = 0 := by
    rw [← map_nsmul, h33]
    exact (hφ₁ker _).mpr (AddSubgroup.mem_zmultiples _)
  have hord₁ : addOrderOf (φ₁ ((3 : ℕ) • g)) = 3 :=
    X0Three.addOrderOf_eq_of_prime (by norm_num) _ hg₁ne hg₁3
  have hst₁ := X0Three.stable_map
    (fun σ : Field.absoluteGaloisGroup ℚ =>
      Affine.Point.map (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom)
    (fun σ : Field.absoluteGaloisGroup ℚ =>
      Affine.Point.map (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom)
    φ₁ hφ₁gal ((3 : ℕ) • g) hst3
  -- STEP 2 : the isogeny with kernel `⟨φ₁(3g)⟩`
  obtain ⟨u₂, E₂, hE₂, φ₂, hφ₂gal, hφ₂ker, hu₂0, hj2, hj2'⟩ :=
    E₁.exists_x0Three_param_of_stableThreeSubgroup (φ₁ ((3 : ℕ) • g)) hord₁ hst₁
  haveI := hE₂
  have hg₂ne : φ₂ (φ₁ g) ≠ 0 := X0Three.map_map_ne_zero φ₁ φ₂ g hg hφ₁ker hφ₂ker
  have hg₂3 : (3 : ℕ) • φ₂ (φ₁ g) = 0 := by
    rw [← map_nsmul, ← map_nsmul]
    exact (hφ₂ker _).mpr (AddSubgroup.mem_zmultiples _)
  have hord₂ : addOrderOf (φ₂ (φ₁ g)) = 3 :=
    X0Three.addOrderOf_eq_of_prime (by norm_num) _ hg₂ne hg₂3
  have hstg1 := X0Three.stable_map
    (fun σ : Field.absoluteGaloisGroup ℚ =>
      Affine.Point.map (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom)
    (fun σ : Field.absoluteGaloisGroup ℚ =>
      Affine.Point.map (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom)
    φ₁ hφ₁gal g hstable
  have hst₂ := X0Three.stable_map
    (fun σ : Field.absoluteGaloisGroup ℚ =>
      Affine.Point.map (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom)
    (fun σ : Field.absoluteGaloisGroup ℚ =>
      Affine.Point.map (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom)
    φ₂ hφ₂gal (φ₁ g) hstg1
  -- STEP 3 : the isogeny with kernel `⟨φ₂(φ₁ g)⟩`
  obtain ⟨u₃, E₃, hE₃, φ₃, hφ₃gal, hφ₃ker, hu₃0, hj3, hj3'⟩ :=
    E₂.exists_x0Three_param_of_stableThreeSubgroup (φ₂ (φ₁ g)) hord₂ hst₂
  haveI := hE₃
  -- non-backtracking of the first consecutive pair, over `⟨3g⟩`
  have hA9 : (9 : ℕ) • ((3 : ℕ) • g) = 0 := by
    rw [h39, ← hg]; exact addOrderOf_nsmul_eq_zero g
  have hA3 : (3 : ℕ) • ((3 : ℕ) • g) ≠ 0 := by rw [h33]; exact h9ne
  have hAker : ∀ Pt : (E⁄(AlgebraicClosure ℚ)).Point,
      φ₁ Pt = 0 ↔ Pt ∈ AddSubgroup.zmultiples ((3 : ℕ) • ((3 : ℕ) • g)) := by
    intro Pt; rw [h33]; exact hφ₁ker Pt
  have hnb1 : u₁ * u₂ ≠ 729 :=
    WeierstrassCurve.x0Three_param_mul_ne_729 E E₁ E₂ φ₁ φ₂ hφ₁gal hφ₂gal
      ((3 : ℕ) • g) hA9 hA3 hst3 hAker hφ₂ker u₁ u₂ hu₁0 hu₂0 hj1 hj1' hj2 hj2'
  -- non-backtracking of the second consecutive pair, over `⟨φ₁ g⟩`
  have hB9 : (9 : ℕ) • φ₁ g = 0 := by
    rw [← map_nsmul]; exact (hφ₁ker _).mpr (AddSubgroup.mem_zmultiples _)
  have hB3 : (3 : ℕ) • φ₁ g ≠ 0 := by rw [← map_nsmul]; exact hg₁ne
  have hBker : ∀ Pt : (E₁⁄(AlgebraicClosure ℚ)).Point,
      φ₂ Pt = 0 ↔ Pt ∈ AddSubgroup.zmultiples ((3 : ℕ) • φ₁ g) := by
    intro Pt; rw [← map_nsmul]; exact hφ₂ker Pt
  have hnb2 : u₂ * u₃ ≠ 729 :=
    WeierstrassCurve.x0Three_param_mul_ne_729 E₁ E₂ E₃ φ₂ φ₃ hφ₂gal hφ₃gal
      (φ₁ g) hB9 hB3 hstg1 hBker hφ₃ker u₂ u₃ hu₂0 hu₃0 hj2 hj2' hj3 hj3'
  exact ⟨u₁, u₂, u₃, hj1,
    X0Three.residual_of_matching E₁.j u₁ u₂ hj1' hj2 hnb1,
    X0Three.residual_of_matching E₂.j u₂ u₃ hj2' hj3 hnb2, hnb1, hnb2⟩

/-- **`X_0(27)`: a rational cyclic `27`-subgroup IS a rational point of
`27a1`, lying over an `X_0(9)`-parameter of `E`** (PROVEN 2026-07-26 over
the single level-`3` leaf `exists_x0Three_chainParameters`; introduced and
restated 2026-07-26):
if `E` carries a `Gal(ℚ̄/ℚ)`-stable cyclic subgroup `C` of order `27`,
then there are rationals `x, y, s` with

* `y² + y = x³ − 7` — a rational point of the model `27a1` of `X_0(27)`;
* `s · x = 4 − 3x − y` — its image under the degree-`3` degeneracy map
  `π₁ : X_0(27) → X_0(9)`, `(x, y) ↦ (4 − 3x − y)/x`, in denominator-free
  form;
* `j(E) · s⁹(s² + 9s + 27) = (s + 9)³(s³ + 243s² + 2187s + 6561)³` —
  compatibility of `π₁` with the two `j`-maps: `s` is an
  `X_0(9)`-parameter of `E`, because `π₁(E, C) = (E, C[9])`.

This is **the moduli dictionary and nothing else**: the pair `(E, C)`
is a non-cuspidal rational point of `X_0(27)`, `27a1 : y² + y = x³ − 7`
is a model of that curve, `π₁` is the degeneracy map in those
coordinates, and its `X_0(9)`-image carries `(E, C[9])`. No Diophantine
input is left in the statement — the Mordell–Weil half is
`MazurLevel27.rational_point_x0TwentySeven` (PROVEN from
`fermatLastTheoremThree`), the fibre-sharpness half is
`MazurLevel27.x0Nine_fibre_over_CM` (PROVEN above), and the two are
assembled in `exists_x0TwentySeven_point` below.

**PROVEN 2026-07-26 over the single level-`3` leaf
`exists_x0Three_chainParameters`**, replacing the previous "irreducible,
needs `X_0(27)` as a scheme" assessment. The route is the `3`-isogeny
chain, and it removes every level above `3` from the frontier:

1. `exists_x0Three_chainParameters` (the remaining leaf) gives the three
   `X_0(3)` hauptmodul parameters `u₁, u₂, u₃` of the chain
   `E → E/C[3] → E/C[9] → E/C`, the `j`-map relation at `u₁`, the two
   consecutive-`j` matching relations in their residual form, and
   non-backtracking `u₁u₂ ≠ 729`, `u₂u₃ ≠ 729`.
2. `MazurLevel27.x0TwentySeven_moduliPoint_of_chainParameters` (PROVEN,
   pure arithmetic over `ℚ`) does everything else: it inverts the `X_0(9)`
   parametrisation `u = s³/(s²+9s+27)`, `v = s(s²+9s+27)` of the residual
   `(3,3)` curve by an explicit rational function, glues the two halves into
   the `X_0(27)` plane model `s₁(s₁²+9s₁+27)(s₂²+9s₂+27) = s₂³`, maps that
   birationally onto `27a1` by `x = (s₂+9)/(s₁+3)`, `y = −s₂−5`, and
   transports the `j`-relation from level `3` to level `9`.

**Cut note for the fleet** (superseding the earlier one, which said the
moduli dictionary was indivisible here). It IS divisible, and the cut is by
LEVEL after all — but downwards, to level `3`, not sideways to level `9`.
What made the earlier level-`9`/level-`27` split a rename is that both
halves still needed a modular curve of positive genus; the level-`3` cut does
not, because `X_0(3)` is `P¹` with an elementary universal family and
because the Fricke involution `w₃ : u ↦ 729/u` — the backtracking component
of the `j`-matching relation — is visible as an explicit factor of an
explicit polynomial. -/
theorem WeierstrassCurve.exists_x0TwentySeven_moduliPoint
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) (hg : addOrderOf g = 27)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    ∃ x y s : ℚ, y ^ 2 + y = x ^ 3 - 7 ∧ s * x = 4 - 3 * x - y ∧
      E.j * (s ^ 9 * (s ^ 2 + 9 * s + 27))
        = (s + 9) ^ 3 * (s ^ 3 + 243 * s ^ 2 + 2187 * s + 6561) ^ 3 := by
  obtain ⟨u₁, u₂, u₃, hj, hG12, hG23, hnb1, hnb2⟩ :=
    E.exists_x0Three_chainParameters g hg hstable
  exact MazurLevel27.x0TwentySeven_moduliPoint_of_chainParameters
    E.j u₁ u₂ u₃ hj hG12 hG23 hnb1 hnb2

/-- **`X_0(27) → X_0(9)`: an `X_0(9)`-parameter of a curve with a
rational cyclic `27`-subgroup lifts to `27a1`** (PROVEN 2026-07-26 over
the single moduli leaf `exists_x0TwentySeven_moduliPoint`): if `E`
carries a `Gal(ℚ̄/ℚ)`-stable cyclic subgroup of order `27`, and `t` is a
rational number lying over `j(E)` under the `X_0(9)` `j`-map, then `t`
is the image of a rational point of `X_0(27) : y² + y = x³ − 7` under
the explicit degeneracy map `π₁ : (x, y) ↦ (4 − 3x − y)/x` — written
denominator-free as `t · x = 4 − 3x − y`.

The hypothesis on `t` is how "`t` is an `X_0(9)`-parameter of `E`" is
said without naming the moduli map: `t` ranges over the fibre of the
degree-`12` map `j₉` above `j(E)`. **That phrasing is sharp, not
weakened, and this is now a theorem rather than a docstring claim**:
`MazurLevel27.x0Nine_fibre_over_CM` proves that the only rational point
of the fibre of `j₉` over `−12288000` is `t = −3`, by factoring the
degree-`12` numerator as `(s + 3)(s² + 27)·Q(s)` and killing the
degree-`9` cofactor `Q` with a congruence modulo `7` on its homogenised
form.

Assembly (this proof), all three steps now proven or reduced to the one
moduli leaf:

1. `exists_x0TwentySeven_moduliPoint` turns the stable cyclic
   `27`-subgroup into a rational point `(x₀, y₀)` of `27a1` together
   with its `π₁`-image `s`, an `X_0(9)`-parameter of `E`.
2. `MazurLevel27.j_eq_of_x0TwentySeven_point` — Fermat's Last Theorem
   for exponent `3`, plus the two evaluations `j₉(0) = ∞` (the rational
   cusp, excluded by the relation itself) and `j₉(−3) = −12288000` —
   reads off `j(E) = −12288000` from that point.
3. `MazurLevel27.x0Nine_fibre_over_CM` then forces the *given* `t` to be
   `−3` as well, where the non-cuspidal point `(x, y) = (3, 4)` of
   `27a1` witnesses the conclusion: `4² + 4 = 3³ − 7` and
   `(−3)·3 = 4 − 3·3 − 4`.

Note that no rank or Mordell–Weil computation is left in this node
either: that half is `MazurLevel27.rational_point_x0TwentySeven`, PROVEN
above from `fermatLastTheoremThree`. -/
theorem WeierstrassCurve.exists_x0TwentySeven_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) (hg : addOrderOf g = 27)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g)
    (t : ℚ)
    (ht : E.j * (t ^ 9 * (t ^ 2 + 9 * t + 27))
      = (t + 9) ^ 3 * (t ^ 3 + 243 * t ^ 2 + 2187 * t + 6561) ^ 3) :
    ∃ x y : ℚ, y ^ 2 + y = x ^ 3 - 7 ∧ t * x = 4 - 3 * x - y := by
  obtain ⟨x₀, y₀, s, hxy₀, hs, hjs⟩ := E.exists_x0TwentySeven_moduliPoint g hg hstable
  have hjval : E.j = -12288000 :=
    MazurLevel27.j_eq_of_x0TwentySeven_point E.j x₀ y₀ s hxy₀ hs hjs
  have htv : t = -3 := by
    refine MazurLevel27.x0Nine_fibre_over_CM t ?_
    rw [← hjval]
    exact ht
  exact ⟨3, 4, by norm_num, by rw [htv]; norm_num⟩

/-- **`X_0(27)`: a rational cyclic `27`-subgroup forces
`j = −12288000`** (PROVEN 2026-07-26 over the two moduli leaves
`exists_x0Nine_hauptmodul` and `exists_x0TwentySeven_point`, replacing
the former `X_1(27)` citation): if the geometric points of an
elliptic curve over `ℚ` contain a point `g` of order `27` whose cyclic
subgroup is `Gal(ℚ̄/ℚ)`-stable, then `j(E) = −12288000`.

Note that `mem_cyclicIsogenyDegrees` gives NOTHING here: `27` IS in
Kenku's list, so the isogeny alone is consistent. What closes the level
is that `X_0(27)` nevertheless has only ONE non-cuspidal rational point,
so the isogeny pins the `j`-invariant.

The pair `(E, ⟨g⟩)` is a non-cuspidal rational point of `X_0(27)`, a
curve of **genus `1`** — namely the elliptic curve `27a1 : y² + y =
x³ − 7`, of Mordell–Weil rank `0` with `X_0(27)(ℚ) ≅ ℤ/3`. Of its six
cusps (`Σ_{d ∣ 27} φ(gcd(d, 27/d)) = 1 + 2 + 2 + 1`) exactly the two of
denominators `1` and `27` are rational, so `X_0(27)` has exactly ONE
non-cuspidal rational point; its image in the `j`-line is the CM value
of discriminant `−27`, `j = −12288000`.

Verified with PARI/GP (2026-07-25, untrusted searcher, statement check
only): `ellisomat` on the conductor-`27` class returns the degree matrix
`[1,3,9,3; 3,1,3,9; 9,3,1,27; 3,9,27,1]`, and the unique `27`-isogeny
joins the curves `[−2430, 184437/4]` and `[−270, −6831/4]`, both of
`j`-invariant `−12288000` — consistent with a single non-cuspidal
rational point of `X_0(27)` realized over `ℚ` by two quadratic twists.

This node is strictly shallower than the `X_1(27)` statement it
replaces: it asks for a rank-`0` Mordell–Weil computation on a genus-`1`
curve rather than the rational points of a genus-`13` curve.

**THE MORDELL–WEIL HALF IS NOW PROVEN, FROM MATHLIB'S FLT₃.** `X_0(27)`
is the FERMAT CUBIC — see the section note above for the change of
variables and the PARI/GP re-derivation — so `#X_0(27)(ℚ) = 3` is
EXACTLY Fermat's Last Theorem for exponent `3`. That half is
`MazurLevel27.rational_point_x0TwentySeven`, PROVEN 2026-07-26 from
`fermatLastTheoremThree`: every rational point of `y² + y = x³ − 7` has
`x = 3` and `y ∈ {4, −5}`.

What remains, and all that remains, is the MODULI INTERPRETATION, split
into the two leaves consumed here:

* `exists_x0Nine_hauptmodul` — level `9`, on the **genus-`0`** curve
  `X_0(9)`: a stable cyclic `9`-subgroup gives a rational Hauptmodul
  value `t` with `j(E) = j₉(t)` for the explicit degree-`12` rational
  function `j₉`. Elementary in principle (universal family over the
  `t`-line plus Vélu), and the natural next target.
* `exists_x0TwentySeven_point` — level `27`: such a `t` is the image of
  a rational point of `27a1 : y² + y = x³ − 7` under the explicit
  degree-`3` degeneracy map `π₁ : (x, y) ↦ (4 − 3x − y)/x`. This is the
  modular-curve content proper.

Assembly (this proof): `3 • g` generates a stable cyclic subgroup of
order `9` (`exists_stable_zmultiples_of_dvd`), which gives `t`; the
level-`27` leaf lifts `t` to a rational point of `27a1`; and
`MazurLevel27.j_eq_of_x0TwentySeven_point` — FLT₃ plus the two explicit
evaluations `j₉(0) = ∞` (the rational cusp, excluded by the relation
itself) and `j₉(−3) = −12288000` — reads off the `j`-invariant. -/
theorem WeierstrassCurve.j_of_stable_cyclic_subgroup_order_27
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) (hg : addOrderOf g = 27)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    E.j = -12288000 := by
  obtain ⟨g₉, hg₉, hstable₉⟩ :=
    E.exists_stable_zmultiples_of_dvd g (N := 27) (d := 9) (by norm_num) (by norm_num) hg hstable
  obtain ⟨t, ht⟩ := E.exists_x0Nine_hauptmodul g₉ hg₉ hstable₉
  obtain ⟨x, y, hxy, htx⟩ := E.exists_x0TwentySeven_point g hg hstable t ht
  exact MazurLevel27.j_eq_of_x0TwentySeven_point E.j x y t hxy htx ht

/-!
##### `X_0(32)` is `y² = x³ + 4x` — the Mordell–Weil half, PROVEN (2026-07-26)

The level-`32` node below is now PROVEN over two moduli leaves, exactly on
the pattern of `j_of_stable_cyclic_subgroup_order_27`. Its *arithmetic*
half — the determination of `X_0(32)(ℚ)` — is no longer a citation: it is
`QuarticDescent.rational_point_x0ThirtyTwo`, proven outright in
`Fermat/FLT/FreyCurve/QuarticDescent.lean`.

Magma's `SmallModularCurve(32)` (2026-07-26, untrusted searcher) returns
`X_0(32) : y² = x³ + 4x`, the conductor-`32` curve, with `rank = 0` and
`torsion ≅ ℤ/4`; so `X_0(32)(ℚ)` is `{O, (0,0), (2,4), (2,−4)}`, and all
four points are cusps (`Σ_{d ∣ 32} φ(gcd(d, 32/d)) = 8` cusps, of which the
`4` with `d ∈ {1, 2, 16, 32}` are rational — exactly the point count).

**Why the rank-`0` half is reachable here and was mis-assessed as
irreducible.** `y² = x³ + 4x` is `2`-isogenous, by the explicit Vélu map
`(x, y) ↦ ((x² + 4)/(4x), y(x² − 4)/(8x²))`, to `y² = x³ − 16x ≅ y² = x³ − x`
— the congruent-number-`1` curve. Its Mordell–Weil determination is
Fermat's *other* quartic theorem `x⁴ − y⁴ ≠ z²`, which this development
already proves by infinite descent. So level `32` stands to Fermat's
quartic theorem exactly as level `27` stands to Fermat's cubic theorem
(`MazurLevel27.rational_point_x0TwentySeven`, from
`fermatLastTheoremThree`). Both Mordell–Weil halves are now PROVEN and only
the moduli dictionary is open.

What is left, and all that is left, is the moduli interpretation, split
into the two leaves consumed below:

* `exists_x0Sixteen_hauptmodul` — level `16`, on the **genus-`0`** curve
  `X_0(16)`: a stable cyclic `16`-subgroup gives a rational Hauptmodul
  value `s` with `j(E) = j₁₆(s)` for the explicit degree-`24` rational
  function `j₁₆`. This is the direct analogue of `exists_x0Nine_hauptmodul`
  and is elementary in principle (the universal curve with a cyclic
  `16`-isogeny over the `s`-line, i.e. an iterated Vélu `2`-isogeny chain).
  **Its hypothesis is satisfiable** — `16`-isogenies exist — so this leaf
  carries genuine content.
* `exists_x0ThirtyTwo_point` — level `32`: such an `s` is the image of a
  rational point of `y² = x³ + 4x` under the degeneracy map
  `π : (x, y) ↦ y/(x² + 4)`. **VACUITY AUDIT: this leaf's hypothesis is
  unsatisfiable** (no curve has a cyclic `32`-isogeny — that is the theorem),
  so the leaf is vacuously true and cannot be proven independently of the
  node it serves. That is unavoidable for any level whose conclusion is
  `False`, and it is the shape every sibling level in this file already has;
  it is recorded here so nobody mistakes it for reducible content. The
  mathematics of the level lives entirely in the two NON-vacuous pieces:
  the `X_0(16)` leaf above and the PROVEN `X_0(32)` Mordell–Weil half.

The `j`-map of `X_0(16)` used below is
`j = M(s)³ / (s (1 − 2s)¹⁶ (1 + 2s)⁴ (1 + 4s²))` with `M` of degree `8`;
`s = 1/(t + 2)` where `t` is Magma's `X_0(16)` Hauptmodul, a Möbius change
chosen so that no rational point of `X_0(32)` is sent to `s = ∞`. Poles of
`j₁₆` at `s = 0, 1/2, −1/2` and at the two conjugate points `s = ∓i/2`, of
orders `1, 16, 4, 1, 1`, plus the simple pole at `s = ∞` (the cusp `t = −2`):
`1 + 16 + 4 + 1 + 1 + 1 = 24 = [SL₂(ℤ) : Γ₀(16)]` ✓. Verified in PARI/GP:
for `s = 1, …, 5, 1/3, 1/4, 1/5` the curve `ellfromj(j₁₆(s))` has cyclic
isogeny degrees exactly `{1, 2, 4, 8, 16}`.
-/

/-- **`X_0(16)`, the genus-`0` level: a rational cyclic `16`-subgroup puts
`j` on the explicit degree-`24` Hauptmodul curve** (sorry node — the moduli
content at level `16`, introduced 2026-07-26): if the geometric points of an
elliptic curve over `ℚ` contain a point `g` of order `16` whose cyclic
subgroup is `Gal(ℚ̄/ℚ)`-stable, then there is a rational number `s` with

  `j(E) · s(1 − 2s)¹⁶(1 + 2s)⁴(1 + 4s²) = M(s)³`,

`M(s) = 256s⁸ + 15360s⁷ + 34560s⁶ + 26880s⁵ + 17504s⁴ + 6720s³ + 2160s²
        + 240s + 1`.

This is the statement that `(E, ⟨g⟩)` is a non-cuspidal rational point of
`X_0(16)`, together with the explicit `j`-map of that modular curve.
`X_0(16)` has **genus `0`** with a `ℚ`-rational cusp, so it is `ℙ¹_ℚ` and a
rational point has a rational `s`-coordinate; `s ≠ ∞` (the cusp `t = −2`) is
forced because `E` is an honest elliptic curve, hence not a cusp, and the
displayed identity itself excludes the remaining cusps `s = 0, 1/2, −1/2`
because `M` does not vanish there (`M(0) = 1`, `M(1/2) = 4096`,
`M(−1/2) = 256`).

Its intended proof is elementary and needs no modular curve as a scheme:
exhibit the universal family over the `s`-line — a curve with a rational
point of order `2` together with Vélu's formulae for the four `2`-isogenies
in the chain `E → E/C₂ → E/C₄ → E/C₈ → E/C₁₆` — and compute its
`j`-invariant. Compare `exists_x0Nine_hauptmodul`, which is the same
statement one level down the `3`-power tower. -/
theorem WeierstrassCurve.exists_x0Sixteen_hauptmodul
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) (hg : addOrderOf g = 16)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    ∃ s : ℚ, E.j * (s * (1 - 2 * s) ^ 16 * (1 + 2 * s) ^ 4 * (1 + 4 * s ^ 2))
      = (256 * s ^ 8 + 15360 * s ^ 7 + 34560 * s ^ 6 + 26880 * s ^ 5 + 17504 * s ^ 4
          + 6720 * s ^ 3 + 2160 * s ^ 2 + 240 * s + 1) ^ 3 :=
  sorry

/-- **`X_0(32) → X_0(16)`: an `X_0(16)`-parameter of a curve with a rational
cyclic `32`-subgroup lifts to `y² = x³ + 4x`** (sorry node — the level-`32`
moduli content, introduced 2026-07-26): if `E` carries a `Gal(ℚ̄/ℚ)`-stable
cyclic subgroup of order `32`, and `s` is a rational number lying over `j(E)`
under the `X_0(16)` `j`-map, then `s` is the image of a rational point of
`X_0(32) : y² = x³ + 4x` under the explicit degeneracy map
`π : (x, y) ↦ y/(x² + 4)` — written denominator-free as `s(x² + 4) = y`.

The map is regular on the whole affine curve because `x² + 4 > 0`, so the
displayed relation is never vacuous at a point; that is why this coordinate
was chosen over the equivalent `t = (y − 2x)/x`, which degenerates at
`(0, 0)`.

This is the node that carries the modular-curve content proper: the
degeneracy map `π : X_0(32) → X_0(16)` of degree `2` and the model
`y² = x³ + 4x` of `X_0(32)`. Its intended proof is the moduli dictionary —
the pair `(E, C)` with `C` cyclic of order `32` gives a rational point of
`X_0(32)` whose image in `X_0(16)` is `(E, 2C)` — for which nothing exists
in this development yet.

**VACUITY AUDIT.** By the very theorem it serves, the hypothesis
`addOrderOf g = 32` together with stability is never satisfied, so this leaf
is vacuously true and is NOT independently provable: whoever proves it will
be proving the moduli dictionary in general and instantiating it. See the
section note above. No rank or Mordell–Weil computation is left in this
node: that half is `QuarticDescent.rational_point_x0ThirtyTwo`, PROVEN from
`QuarticDescent.sq_ne_quartic_sub_quartic`.

**AUDIT OF THE AUDIT: THE VACUITY IS FORCED, AND THIS CUT IS ALREADY
OPTIMAL** (2026-07-26, in answer to the standing question of whether this
leaf should exist in this form at all).

The general fact, which settles it: *if `P` is unsatisfiable then `P → R` is
vacuous for **every** `R`.* So in any two-step decomposition of a node
`P → False` with `P` unsatisfiable — and `P` = "`E` carries a stable cyclic
`32`-subgroup" is unsatisfiable, that being the theorem — the first step is
vacuous no matter what intermediate `R` is chosen. Vacuity here is therefore
a property of the LEVEL (every prime power absent from the Mazur–Kenku list
has conclusion `False`), not a defect of this particular cut, and no
restatement of this leaf can remove it. Contrast level `27`, where the
analogous leaf `exists_x0TwentySeven_point` has the SATISFIABLE hypothesis
"stable cyclic `27`-subgroup" (`27` IS in the list) and correspondingly the
intermediate conclusion `j = −12288000` rather than `False`; that is why the
level-`27` glue node carries content and this one cannot.

What CAN be optimised is where the content sits, and it already sits in the
right places. All of it is in the two siblings, both of which escape the
vacuity:

* `exists_x0Sixteen_hauptmodul` — hypothesis "stable cyclic `16`-subgroup",
  **satisfiable** (`16`-isogenies exist), so genuinely provable in isolation,
  and elementary in principle: the universal family over the `s`-line;
* `QuarticDescent.no_x0ThirtyTwo_point` — a statement about rational
  numbers only, no curve hypothesis at all, **PROVEN** from Fermat's other
  quartic theorem.

Two restructurings were considered and REJECTED for concrete reasons.
(i) Merging this leaf into `exists_x0Sixteen_hauptmodul` (one leaf instead of
two) would drop the frontier by one, but it would convert the one
independently PROVABLE node of the level into an unprovable-in-isolation one
— trading real progress for a count. (ii) Restating the degeneracy step as
an equivalence "the `16`-subgroup extends to a `32`-subgroup **iff** `s`
lifts" does not help either: the `s` that lift are exactly the three cusps
`0, ±1/2`, over which no elliptic curve sits, so both directions have
unsatisfiable hypotheses and the `↔` is vacuous as well.

Conclusion: keep this leaf, exactly as stated. It is the irreducible glue of
a `False`-conclusion level, it is TRUE, and it relocates no burden — the
sibling that carries content is specified for exactly the content it
carries. Do not dispatch a prover at it in isolation; it closes only as a
corollary of a general moduli dictionary for `X_0(N)`, which does not exist
in this development. -/
theorem WeierstrassCurve.exists_x0ThirtyTwo_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) (hg : addOrderOf g = 32)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g)
    (s : ℚ)
    (hs : E.j * (s * (1 - 2 * s) ^ 16 * (1 + 2 * s) ^ 4 * (1 + 4 * s ^ 2))
      = (256 * s ^ 8 + 15360 * s ^ 7 + 34560 * s ^ 6 + 26880 * s ^ 5 + 17504 * s ^ 4
          + 6720 * s ^ 3 + 2160 * s ^ 2 + 240 * s + 1) ^ 3) :
    ∃ x y : ℚ, y ^ 2 = x ^ 3 + 4 * x ∧ s * (x ^ 2 + 4) = y :=
  sorry

/-- **No rational cyclic `32`-isogeny** (PROVEN 2026-07-26 over the two
moduli leaves `exists_x0Sixteen_hauptmodul` and `exists_x0ThirtyTwo_point`,
replacing the former Ogg citation): no elliptic curve over `ℚ` carries a
Galois-stable cyclic subgroup of order `32`.

`32 = 2⁵` is the smallest power of `2` absent from the Mazur–Kenku list
(`2, 4, 8, 16` are all present — realized simultaneously by the
conductor-`45` curve `[1,−1,0,0,−5]`, whose cyclic isogeny degrees are
`{1,2,4,8,16}`, as already recorded in the section note above), so by
divisor descent this single statement disposes of every `2^k` with
`k ≥ 5`.

Assembly (this proof): `2 • g` generates a stable cyclic subgroup of order
`16` (`exists_stable_zmultiples_of_dvd`), which gives the `X_0(16)`
Hauptmodul value `s`; the level-`32` leaf lifts `s` to a rational point of
`y² = x³ + 4x`; and `QuarticDescent.no_x0ThirtyTwo_point` — Fermat's quartic
theorem, through the `2`-isogeny to `y² = x³ − x`, plus the three explicit
cusp evaluations `M(0)³`, `M(1/2)³`, `M(−1/2)³` — closes it. See the section
note above for the modular data and its PARI/GP and Magma cross-checks. -/
theorem WeierstrassCurve.not_cyclicIsogeny_thirtyTwo (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (g : (E⁄(AlgebraicClosure ℚ)).Point) (hg : addOrderOf g = 32)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    False := by
  obtain ⟨g₁₆, hg₁₆, hstable₁₆⟩ :=
    E.exists_stable_zmultiples_of_dvd g (N := 32) (d := 16) (by norm_num) (by norm_num)
      hg hstable
  obtain ⟨s, hs⟩ := E.exists_x0Sixteen_hauptmodul g₁₆ hg₁₆ hstable₁₆
  obtain ⟨x, y, hxy, hsx⟩ := E.exists_x0ThirtyTwo_point g hg hstable s hs
  exact QuarticDescent.no_x0ThirtyTwo_point E.j s x y hxy hsx hs

/-- **No rational cyclic `81`-isogeny on the CM `j`-line `j = −12288000`**
(sorry node — the residue of `not_cyclicIsogeny_eightyOne` after the
degree-`3` degeneracy map `X_0(81) → X_0(27)`, introduced 2026-07-26): an
elliptic curve over `ℚ` with `j = −12288000` carries no Galois-stable
cyclic subgroup of order `81`.

**This is the whole of level `81`, and it is strictly shallower than the
statement it serves**: instead of the rational points of the genus-`4`
curve `X_0(81)` (`μ = 108`, `ν₂ = ν₃ = 0`, `12` cusps, `g = 1 + 9 − 6 = 4`)
it asks only for the fibre of `X_0(81) → X_0(27)` over the single
non-cuspidal rational point of `X_0(27)` — three geometric points instead
of a Chabauty/Jacobian-rank computation. The reduction is performed in
`not_cyclicIsogeny_eightyOne` below, over
`j_of_stable_cyclic_subgroup_order_27`, which is now declared ABOVE this
point (the level-`27` cluster was hoisted on 2026-07-26 for exactly this
reason).

**The statement is true, and it is the CM theory that makes it so.**
`j = −12288000` is the CM value of the order of discriminant `−27`
(conductor `3` in `ℚ(√−3)`), and the `3`-power isogeny ladder of that order
stops at `27`. Cross-checked twice with untrusted searchers: PARI/GP
(2026-07-25) gives `ellisomat` degree matrix
`[1,3,9,3; 3,1,3,9; 9,3,1,27; 3,9,27,1]`, and Magma (2026-07-26)
`IsogenousCurves(EllipticCurveWithjInvariant(-12288000))` returns exactly
**four** curves — two of `j = −12288000` and two of `j = 0` — so the longest
cyclic `3`-power chain in the class has `4` vertices and degree `27`. A
cyclic `81`-isogeny would need a chain of `5`. Quadratic twisting permutes
an isogeny class without changing its shape, so this covers every curve over
`ℚ` with this `j`, not merely the minimal model.

**Intended proof.** `E[3^∞]` for a CM curve is governed by the order
`ℤ[(1+3√−3)/2]` of discriminant `−27`: a stable cyclic subgroup of order
`3^k` corresponds to a proper cyclic ideal of `3`-power norm, and the ideal
`(√−3)` is ramified with `(√−3)³` already non-proper for the order of
conductor `3`. Concretely, and closer to what this development can state:
a stable cyclic `81`-subgroup would produce a stable cyclic `27`-subgroup
of `E/⟨27 • g⟩`, another curve of `j`-invariant in the class above, whose
`27`-isogeny partner would extend the ladder past its length `4`.
(Kenku's series, 1979–1982.) -/
theorem WeierstrassCurve.not_cyclicIsogeny_eightyOne_of_j (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (hj : E.j = -12288000)
    (g : (E⁄(AlgebraicClosure ℚ)).Point) (hg : addOrderOf g = 81)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    False :=
  sorry

/-- **No rational cyclic `81`-isogeny** (PROVEN 2026-07-26 over the single
`j`-line leaf `not_cyclicIsogeny_eightyOne_of_j`, replacing the former
Kenku citation): no elliptic curve over `ℚ` carries a Galois-stable cyclic
subgroup of order `81`.

`81 = 3⁴` is the smallest power of `3` absent from the Mazur–Kenku list
(`3, 9, 27` are all present — `27` by the isogeny class `27a`), so by
divisor descent this single statement disposes of every `3^k` with
`k ≥ 4`.

Assembly (this proof), the degree-`3` degeneracy map `X_0(81) → X_0(27)`
written out: `3 • g` generates a Galois-stable cyclic subgroup of order `27`
(`exists_stable_zmultiples_of_dvd`), so
`j_of_stable_cyclic_subgroup_order_27` — the `X_0(27)` node, itself PROVEN
over the genus-`0` leaf `exists_x0Nine_hauptmodul`, the level-`27` moduli
leaf and Fermat's Last Theorem for exponent `3` — pins `j(E) = −12288000`,
and the leaf above closes the single remaining `j`-line. This is what
replaces a Mordell–Weil computation on the genus-`4` curve `X_0(81)`. -/
theorem WeierstrassCurve.not_cyclicIsogeny_eightyOne (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (g : (E⁄(AlgebraicClosure ℚ)).Point) (hg : addOrderOf g = 81)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    False := by
  obtain ⟨g₂₇, hg₂₇, hstable₂₇⟩ :=
    E.exists_stable_zmultiples_of_dvd g (N := 81) (d := 27) (by norm_num) (by norm_num)
      hg hstable
  exact E.not_cyclicIsogeny_eightyOne_of_j
    (E.j_of_stable_cyclic_subgroup_order_27 g₂₇ hg₂₇ hstable₂₇) g hg hstable

/-- **No rational cyclic `125`-isogeny** (sorry node — the level
`X_0(125)` of Kenku's prime-power determination): no elliptic curve over
`ℚ` carries a Galois-stable cyclic subgroup of order `125`.

`125 = 5³` is the smallest power of `5` absent from the Mazur–Kenku list
(`5` and `25` are present, `25` by the isogeny class `11a`), so by
divisor descent this single statement disposes of every `5^k` with
`k ≥ 3`.

IRREDUCIBLE at this mathlib pin: `X_0(125)` has genus `8` (recomputed
2026-07-25: `μ = 150`, `ν₂ = 2`, `ν₃ = 0`, `10` cusps, so
`g = 1 + 25/2 − 1/2 − 5 = 8`). This is precisely the level treated in
Kenku, "On the modular curves `X_0(125)`, `X_1(25)` and `X_1(49)`",
J. London Math. Soc. (2) 23 (1981), 415–427.

**Why this level is the hardest of the four prime powers, checked
2026-07-26.** The other three all admit a reduction that shrinks the
modular curve: level `32` drops to the genus-`0` curve `X_0(16)` plus a
genus-`1` Mordell–Weil determination that is Fermat's quartic theorem (now
PROVEN, see above); level `81` drops to a single `j`-invariant through the
genus-`1` curve `X_0(27)`; the `p²` level drops to nine explicit primes
through Mazur. Here the intermediate level is `X_0(25)`, which has genus
`0` — so it pins nothing, and there are infinitely many curves with a
cyclic `25`-isogeny. The genus-`8` curve `X_0(125)` therefore has to be
faced directly (Kenku works through its Atkin–Lehner quotient). Splitting
this node along `X_0(25)` would produce a genus-`0` Hauptmodul leaf plus a
level-`125` leaf carrying the entire content — a decomposition that
relocates the work without reducing it, so it was deliberately NOT done. -/
theorem WeierstrassCurve.not_cyclicIsogeny_oneHundredTwentyFive
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) (hg : addOrderOf g = 125)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    False :=
  sorry

/-- **No rational cyclic `p²`-isogeny at the nine isogeny primes `≥ 7`**
(sorry node — the levels `X_0(p²)` of Kenku's prime-power determination,
introduced 2026-07-26 as the residue of
`not_cyclicIsogeny_sq_of_prime_ge_seven` after Mazur's prime node): for
`p ∈ {7, 11, 13, 17, 19, 37, 43, 67, 163}`, no elliptic curve over `ℚ`
carries a Galois-stable cyclic subgroup of order `p²`.

This is strictly shallower than the statement it serves: the uniform
quantifier over all primes `p ≥ 7` has been discharged (a cyclic
`p²`-isogeny yields a cyclic `p`-isogeny by divisor descent, and Mazur's
`prime_mem_cyclicIsogenyDegrees` then confines `p` to
`{2, 3, 5, 7, 11, 13, 17, 19, 37, 43, 67, 163}`, of which `p ≥ 7` leaves
nine). What remains is nine concrete modular curves rather than infinitely
many.

The two smallest cases are the classical ones — `X_0(49)` has genus `1`
(`μ = 56`, `ν₂ = 0`, `ν₃ = 2`, `8` cusps; it is the conductor-`49` CM curve,
of rank `0` with `X_0(49)(ℚ) ≅ ℤ/2`, and its two rational points are exactly
its two rational cusps) and `X_0(169)` genus `8` (`μ = 182`,
`ν₂ = ν₃ = 2`, `14` cusps), the latter being exactly Kenku, "The modular
curve `X_0(169)` and rational isogeny", J. London Math. Soc. (2) 22 (1980),
239–244. For the seven larger `p` the input is that only finitely many
`j`-invariants admit a rational `p`-isogeny at all, all of them known
explicitly and all CM except at `p = 17` and `p = 37`, and none of them
admits a cyclic `p²`-isogeny.

A route worth recording, since it is what makes the nine levels finite work
rather than nine independent Chabauty computations: a cyclic `p²`-subgroup
`C` makes `E/C[p]` carry TWO independent `p`-isogenies (with characters
`λ̄` and `χλ̄⁻¹`), i.e. `E'[p]` is diagonalisable over `ℚ`; conversely two
independent `p`-isogenies compose to a cyclic `p²`-isogeny. So the whole
statement is "no elliptic curve over `ℚ` has diagonal mod-`p` representation
for `p ≥ 7`", which is a statement about the isogeny characters this file
already manufactures in `exists_isogenyCharacter`.

IRREDUCIBLE at this mathlib pin: every known route still runs through the
rational points of a modular curve of genus `≥ 1`, or through the CM theory
that classifies the `j`-invariants with a rational `p`-isogeny; neither
exists in this development. -/
theorem WeierstrassCurve.not_cyclicIsogeny_sq_of_isogenyPrime
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) {p : ℕ}
    (hp : p ∈ ({7, 11, 13, 17, 19, 37, 43, 67, 163} : Finset ℕ))
    (hg : addOrderOf g = p ^ 2)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    False :=
  sorry

/-- **No rational cyclic `p²`-isogeny for `p ≥ 7`** (PROVEN 2026-07-26 over
the strictly narrower leaf `not_cyclicIsogeny_sq_of_isogenyPrime`): for a
prime `p ≥ 7`, no elliptic curve over `ℚ` carries a Galois-stable cyclic
subgroup of order `p²`.

Together with the three explicit levels above this is the whole
prime-power half: the composite prime powers in the Mazur–Kenku list are
`4, 8, 9, 16, 25, 27`, all supported on `p ∈ {2, 3, 5}`, so for `p ≥ 7`
even the square is already excluded, and divisor descent removes every
higher power at once.

The uniform quantifier over primes is what is discharged here: `p • g`
generates a stable cyclic subgroup of order `p`
(`exists_stable_zmultiples_of_dvd`), so Mazur's
`prime_mem_cyclicIsogenyDegrees` puts `p` in
`{2, 3, 5, 7, 11, 13, 17, 19, 37, 43, 67, 163}`, and `7 ≤ p` cuts that to
the nine primes of the leaf above. The remaining content is nine explicit
modular curves; see that leaf's docstring. -/
theorem WeierstrassCurve.not_cyclicIsogeny_sq_of_prime_ge_seven
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hg : addOrderOf g = p ^ 2)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    False := by
  obtain ⟨g', hg', hstable'⟩ :=
    E.exists_stable_zmultiples_of_dvd g (N := p ^ 2) (d := p)
      (pow_ne_zero 2 hp.pos.ne') (dvd_pow_self p two_ne_zero) hg hstable
  have hmem := E.prime_mem_cyclicIsogenyDegrees g' hp hg' hstable'
  refine E.not_cyclicIsogeny_sq_of_isogenyPrime g ?_ hg hstable
  fin_cases hmem <;> simp_all

/-!
##### Kenku's non-prime-power half, split into its individual levels (2026-07-25)

`notPrimePow_mem_cyclicIsogenyDegrees` is now PROVEN from twelve shallower
nodes plus one piece of elementary arithmetic proven here
(`kenku_notPrimePow_arithmetic`), again over divisor descent
(`exists_stable_zmultiples_of_dvd`).

Divisor descent says the rational cyclic isogeny degrees are closed under
divisors, so a level `N` is excluded the moment ANY divisor of `N` is. What
must therefore be supplied are the MINIMAL non-prime-power levels absent
from the Mazur–Kenku list `{1, …, 19, 21, 25, 27, 37, 43, 67, 163}`, and
they fall into exactly two families:

* one UNIFORM family — `p * q` for distinct primes with
  `p * q ∉ {6, 10, 14, 15, 21}` (`not_cyclicIsogeny_prod_two_primes`); the
  five listed products are precisely the squarefree semiprimes that do
  occur. This single node also does the work of Mazur's prime node here: it
  forces every prime factor of a non-prime-power level into `{2, 3, 5, 7}`
  by itself, so `prime_mem_cyclicIsogenyDegrees` is NOT needed below.
* eleven CONCRETE levels — the minimal absent ones carrying a repeated
  prime or a third prime: `20, 24, 28, 30, 36, 42, 45, 50, 54, 63, 75`.
  Each has every proper divisor in the list, so none of the eleven is
  implied by another.

The reassembly, proven below in `kenku_notPrimePow_arithmetic`, is pure `ℕ`
arithmetic: `¬ IsPrimePow N` with `2 ≤ N` gives at least two distinct prime
factors; pairing each prime factor with a second one and applying the
uniform node bounds every prime factor by `10` and then pins it into
`{2, 3, 5, 7}`, and the same node excludes `{5, 7}` as a pair (`35`); three
distinct prime factors would force `30 ∣ N` or `42 ∣ N`. So
`N = p ^ a * q ^ b` with `{p, q} ∈ {{2,3}, {2,5}, {2,7}, {3,5}, {3,7}}`, and
the exponents are pinned by the concrete levels: `24, 36, 54` give
`N ∈ {6, 12, 18}`; `20, 50` give `N = 10`; `28` and `49` — the latter from
`not_cyclicIsogeny_sq_of_prime_ge_seven` at `p = 7` — give `N = 14`;
`45, 75` give `N = 15`; `63` and `49` give `N = 21`.

Genera of the eleven concrete levels, computed from
`g = 1 + μ/12 − ν₂/4 − ν₃/3 − ν_∞/2` and cross-checked against
`dim S₂(Γ₀(N))` in PARI/GP (2026-07-25, both agreeing on all eleven):
`X_0(20)`, `X_0(24)`, `X_0(36)` have genus `1`; `X_0(28)`, `X_0(50)` genus
`2`; `X_0(30)`, `X_0(45)` genus `3`; `X_0(54)` genus `4`; `X_0(42)`,
`X_0(63)`, `X_0(75)` genus `5`. Every one is therefore a Mordell–Weil or
Chabauty computation on a curve of positive genus; none is elementary, and
none is reachable at this mathlib pin. The genus-`1` levels are Ogg,
"Rational points on certain elliptic modular curves", Proc. Sympos. Pure
Math. 24 (1973); the higher ones run through Ogg, "Hyperelliptic modular
curves", Bull. Soc. Math. France 102 (1974) and Kenku's series, and the
classification is completed in Kenku, "On the number of `ℚ`-isomorphism
classes of elliptic curves in each `ℚ`-isogeny class", J. Number Theory 15
(1982).
-/

/-- **No rational cyclic `pq`-isogeny outside `{6, 10, 14, 15, 21}`**
(sorry node — the uniform, squarefree part of Kenku's non-prime-power
determination): if `⟨g⟩` is a Galois-stable cyclic subgroup of order `p * q`
for DISTINCT primes `p, q`, then `p * q ∈ {6, 10, 14, 15, 21}`.

Those five are exactly the products of two distinct primes in the
Mazur–Kenku list `{1, …, 19, 21, 25, 27, 37, 43, 67, 163}` (the list's
other non-prime-powers, `12 = 2² · 3` and `18 = 2 · 3²`, are not
squarefree).

The statement is uniform but its content is finite: by Mazur's prime node
both `p` and `q` lie in `{2, 3, 5, 7, 11, 13, 17, 19, 37, 43, 67, 163}`, so
`61` of the `66` unordered pairs have to be excluded — among them `X_0(35)`
and `X_0(39)` (Kenku, Math. Proc. Cambridge Philos. Soc. 85, 1979),
`X_0(65)` and `X_0(91)` (ibid. 87, 1980).

IRREDUCIBLE at this mathlib pin: each excluded pair is a determination of
`X_0(pq)(ℚ)` at a level of genus `≥ 1` (already `X_0(22)` has genus `2`),
and neither modular curves nor their Jacobians exist in this development. -/
theorem WeierstrassCurve.not_cyclicIsogeny_prod_two_primes (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (g : (E⁄(AlgebraicClosure ℚ)).Point) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hg : addOrderOf g = p * q)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    p * q ∈ ({6, 10, 14, 15, 21} : Finset ℕ) :=
  sorry

/-- **No rational cyclic `20`-isogeny** (sorry node — the level `X_0(20)`,
genus `1`). Minimal absent level: every proper divisor of `20`, namely
`1, 2, 4, 5, 10`, lies in the Mazur–Kenku list. IRREDUCIBLE at this mathlib
pin (Ogg 1973; no modular curve exists here). -/
theorem WeierstrassCurve.not_cyclicIsogeny_twenty (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (g : (E⁄(AlgebraicClosure ℚ)).Point) (hg : addOrderOf g = 20)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    False :=
  sorry

/-- **No rational cyclic `24`-isogeny** (sorry node — the level `X_0(24)`,
genus `1`). Minimal absent level: every proper divisor of `24`, namely
`1, 2, 3, 4, 6, 8, 12`, lies in the Mazur–Kenku list. IRREDUCIBLE at this
mathlib pin (Ogg 1973; no modular curve exists here). -/
theorem WeierstrassCurve.not_cyclicIsogeny_twentyFour (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (g : (E⁄(AlgebraicClosure ℚ)).Point) (hg : addOrderOf g = 24)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    False :=
  sorry

/-- **No rational cyclic `28`-isogeny** (sorry node — the level `X_0(28)`,
genus `2`). Minimal absent level: every proper divisor of `28`, namely
`1, 2, 4, 7, 14`, lies in the Mazur–Kenku list. IRREDUCIBLE at this mathlib
pin: a genus-`2` Jacobian/Chabauty computation (Ogg 1974; Kenku 1979–1982),
and nothing of the kind exists in this development. -/
theorem WeierstrassCurve.not_cyclicIsogeny_twentyEight (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (g : (E⁄(AlgebraicClosure ℚ)).Point) (hg : addOrderOf g = 28)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    False :=
  sorry

/-- **No rational cyclic `30`-isogeny** (sorry node — the level `X_0(30)`,
genus `3`). This is the minimal level with THREE distinct prime factors:
every proper divisor of `30`, namely `1, 2, 3, 5, 6, 10, 15`, lies in the
Mazur–Kenku list. Together with `not_cyclicIsogeny_fortyTwo` it is what
rules out three distinct primes altogether, once the pair node has confined
the primes to `{2, 3, 5, 7}` and killed `{5, 7}`. IRREDUCIBLE at this
mathlib pin: a genus-`3` Chabauty computation. -/
theorem WeierstrassCurve.not_cyclicIsogeny_thirty (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (g : (E⁄(AlgebraicClosure ℚ)).Point) (hg : addOrderOf g = 30)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    False :=
  sorry

/-- **No rational cyclic `36`-isogeny** (sorry node — the level `X_0(36)`,
genus `1`). Minimal absent level: every proper divisor of `36`, namely
`1, 2, 3, 4, 6, 9, 12, 18`, lies in the Mazur–Kenku list. IRREDUCIBLE at
this mathlib pin (Ogg 1973; no modular curve exists here). -/
theorem WeierstrassCurve.not_cyclicIsogeny_thirtySix (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (g : (E⁄(AlgebraicClosure ℚ)).Point) (hg : addOrderOf g = 36)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    False :=
  sorry

/-- **No rational cyclic `42`-isogeny** (sorry node — the level `X_0(42)`,
genus `5`). The second minimal level with three distinct prime factors:
every proper divisor of `42`, namely `1, 2, 3, 6, 7, 14, 21`, lies in the
Mazur–Kenku list. IRREDUCIBLE at this mathlib pin: a genus-`5` Chabauty
computation. -/
theorem WeierstrassCurve.not_cyclicIsogeny_fortyTwo (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (g : (E⁄(AlgebraicClosure ℚ)).Point) (hg : addOrderOf g = 42)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    False :=
  sorry

/-- **No rational cyclic `45`-isogeny** (sorry node — the level `X_0(45)`,
genus `3`). Minimal absent level: every proper divisor of `45`, namely
`1, 3, 5, 9, 15`, lies in the Mazur–Kenku list. IRREDUCIBLE at this mathlib
pin: a genus-`3` Chabauty computation. -/
theorem WeierstrassCurve.not_cyclicIsogeny_fortyFive (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (g : (E⁄(AlgebraicClosure ℚ)).Point) (hg : addOrderOf g = 45)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    False :=
  sorry

/-- **No rational cyclic `50`-isogeny** (sorry node — the level `X_0(50)`,
genus `2`). Minimal absent level: every proper divisor of `50`, namely
`1, 2, 5, 10, 25`, lies in the Mazur–Kenku list. IRREDUCIBLE at this mathlib
pin: a genus-`2` Jacobian/Chabauty computation (Ogg 1974). -/
theorem WeierstrassCurve.not_cyclicIsogeny_fifty (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (g : (E⁄(AlgebraicClosure ℚ)).Point) (hg : addOrderOf g = 50)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    False :=
  sorry

/-- **No rational cyclic `54`-isogeny** (sorry node — the level `X_0(54)`,
genus `4`). Minimal absent level: every proper divisor of `54`, namely
`1, 2, 3, 6, 9, 18, 27`, lies in the Mazur–Kenku list. IRREDUCIBLE at this
mathlib pin: a genus-`4` Chabauty computation. -/
theorem WeierstrassCurve.not_cyclicIsogeny_fiftyFour (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (g : (E⁄(AlgebraicClosure ℚ)).Point) (hg : addOrderOf g = 54)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    False :=
  sorry

/-- **No rational cyclic `63`-isogeny** (sorry node — the level `X_0(63)`,
genus `5`). Minimal absent level: every proper divisor of `63`, namely
`1, 3, 7, 9, 21`, lies in the Mazur–Kenku list. IRREDUCIBLE at this mathlib
pin: a genus-`5` Chabauty computation. -/
theorem WeierstrassCurve.not_cyclicIsogeny_sixtyThree (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (g : (E⁄(AlgebraicClosure ℚ)).Point) (hg : addOrderOf g = 63)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    False :=
  sorry

/-- **No rational cyclic `75`-isogeny** (sorry node — the level `X_0(75)`,
genus `5`). Minimal absent level: every proper divisor of `75`, namely
`1, 3, 5, 15, 25`, lies in the Mazur–Kenku list. IRREDUCIBLE at this mathlib
pin: a genus-`5` Chabauty computation. -/
theorem WeierstrassCurve.not_cyclicIsogeny_seventyFive (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (g : (E⁄(AlgebraicClosure ℚ)).Point) (hg : addOrderOf g = 75)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    False :=
  sorry

/-- **The arithmetic reassembly of Kenku's non-prime-power half** (PROVEN
2026-07-25). This is a statement about natural numbers only: no elliptic
curve appears. It takes the twelve exclusions supplied by the nodes above —
transported along divisor descent to every DIVISOR of `N` — and reconstructs
the seven-element conclusion.

`hpair` is `not_cyclicIsogeny_prod_two_primes` at every pair of distinct
primes dividing `N`; `h49` is `not_cyclicIsogeny_sq_of_prime_ge_seven` at
`p = 7`; the rest are the eleven concrete levels.

The argument: `¬ IsPrimePow N` and `2 ≤ N` make `N.primeFactors` nontrivial
(`Nat.not_isPrimePow_iff_nontrivial_of_two_le`); pairing an arbitrary prime
factor with a second one and feeding `hpair` bounds both by `10` (from
`p * q ≤ 21`) and then pins them into `{2, 3, 5, 7}` by decision; `hpair`
also kills `{5, 7}`, and `h30`/`h42` kill every triple. What is left is
`N = p ^ a * q ^ b` over five pairs — the factorisation being
`Nat.prod_factorization_pow_eq_self` restricted to a two-element support —
with the exponents pinned by the remaining nine exclusions through
`Nat.ordProj_dvd` and coprime multiplication. -/
theorem WeierstrassCurve.kenku_notPrimePow_arithmetic (N : ℕ) (hN : 2 ≤ N)
    (hpp : ¬ IsPrimePow N)
    (hpair : ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → p * q ∣ N →
      p * q ∈ ({6, 10, 14, 15, 21} : Finset ℕ))
    (h49 : ¬ (49 ∣ N)) (h20 : ¬ (20 ∣ N)) (h24 : ¬ (24 ∣ N)) (h28 : ¬ (28 ∣ N))
    (h30 : ¬ (30 ∣ N)) (h36 : ¬ (36 ∣ N)) (h42 : ¬ (42 ∣ N)) (h45 : ¬ (45 ∣ N))
    (h50 : ¬ (50 ∣ N)) (h54 : ¬ (54 ∣ N)) (h63 : ¬ (63 ∣ N)) (h75 : ¬ (75 ∣ N)) :
    N ∈ ({6, 10, 12, 14, 15, 18, 21} : Finset ℕ) := by
  have hN0 : N ≠ 0 := by omega
  have hstruct : ∀ p q : ℕ, p ≠ q → N.primeFactors ⊆ ({p, q} : Finset ℕ) →
      N = p ^ N.factorization p * q ^ N.factorization q := by
    intro p q hpq hsub
    have hsupp : N.factorization.support ⊆ ({p, q} : Finset ℕ) := by
      rw [Nat.support_factorization]; exact hsub
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hN0]
    rw [Finsupp.prod_of_support_subset _ hsupp _ (fun i _ => pow_zero i), Finset.prod_pair hpq]
  have hmul : ∀ u v : ℕ, Nat.Coprime u v → u ∣ N → v ∣ N → u * v ∣ N :=
    fun u v h hu hv => Nat.Coprime.mul_dvd_of_dvd_of_dvd h hu hv
  have hcon : ∀ u v w : ℕ, Nat.Coprime u v → u * v = w → u ∣ N → v ∣ N → ¬ (w ∣ N) → False :=
    fun u v w hc he hu hv hw => hw (he ▸ hmul u v hc hu hv)
  have hdp : ∀ p k : ℕ, k ≤ N.factorization p → p ^ k ∣ N := fun p k hk =>
    dvd_trans (pow_dvd_pow p hk) (Nat.ordProj_dvd N p)
  have hd : ∀ p, p ∈ N.primeFactors → p ∣ N := fun p hp => Nat.dvd_of_mem_primeFactors hp
  have hposfac : ∀ p, p ∈ N.primeFactors → 1 ≤ N.factorization p := by
    intro p hp
    have h : N.factorization p ≠ 0 := by
      rw [← Finsupp.mem_support_iff, Nat.support_factorization]; exact hp
    omega
  -- the pairwise constraint, transported to prime factors
  have key : ∀ p q : ℕ, p ∈ N.primeFactors → q ∈ N.primeFactors → p ≠ q →
      p * q ∈ ({6, 10, 14, 15, 21} : Finset ℕ) := by
    intro p q hp hq hne
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hq' := Nat.prime_of_mem_primeFactors hq
    exact hpair p q hp' hq' hne
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hp' hq').mpr hne)
        (Nat.dvd_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hq))
  have hnt : N.primeFactors.Nontrivial :=
    (Nat.not_isPrimePow_iff_nontrivial_of_two_le hN).mp hpp
  have hcard : 1 < N.primeFactors.card := Finset.one_lt_card_iff_nontrivial.mpr hnt
  have hex : ∀ p : ℕ, ∃ q ∈ N.primeFactors, q ≠ p := by
    intro p
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
    rcases eq_or_ne a p with rfl | h
    · exact ⟨b, hb, Ne.symm hab⟩
    · exact ⟨a, ha, h⟩
  -- every prime factor lies in `{2, 3, 5, 7}`
  have hsub : ∀ p, p ∈ N.primeFactors → p ∈ ({2, 3, 5, 7} : Finset ℕ) := by
    intro p hp
    obtain ⟨q, hq, hne⟩ := hex p
    have hk := key q p hq hp hne
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hq2 : 2 ≤ q := (Nat.prime_of_mem_primeFactors hq).two_le
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    have hple : p ≤ 10 := by
      have h1 : 2 * p ≤ q * p := Nat.mul_le_mul_right p hq2
      rcases hk with h | h | h | h | h <;> rw [h] at h1 <;> omega
    have hqle : q ≤ 10 := by
      have h1 : q * 2 ≤ q * p := Nat.mul_le_mul_left q hp2
      rcases hk with h | h | h | h | h <;> rw [h] at h1 <;> omega
    clear hp hq hne
    interval_cases p <;> interval_cases q <;> revert hk <;> decide
  by_cases b2 : 2 ∈ N.primeFactors
  · by_cases b3 : 3 ∈ N.primeFactors
    · -- prime factors `{2, 3}`
      have h2 : (2:ℕ) ∣ N := hd 2 b2
      have h3 : (3:ℕ) ∣ N := hd 3 b3
      have h6 : (6:ℕ) ∣ N := by simpa using hmul 2 3 (by decide) h2 h3
      have b5 : 5 ∉ N.primeFactors := fun h =>
        hcon 6 5 30 (by decide) (by norm_num) h6 (hd 5 h) h30
      have b7 : 7 ∉ N.primeFactors := fun h =>
        hcon 6 7 42 (by decide) (by norm_num) h6 (hd 7 h) h42
      have hsub23 : N.primeFactors ⊆ ({2, 3} : Finset ℕ) := by
        intro r hr
        have h := hsub r hr
        simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
        rcases h with rfl | rfl | rfl | rfl
        exacts [Or.inl rfl, Or.inr rfl, absurd hr b5, absurd hr b7]
      have ha1 : 1 ≤ N.factorization 2 := hposfac 2 b2
      have hb1 : 1 ≤ N.factorization 3 := hposfac 3 b3
      have ha2 : N.factorization 2 ≤ 2 := by
        by_contra hc
        exact hcon 8 3 24 (by decide) (by norm_num)
          (by simpa using hdp 2 3 (by omega)) h3 h24
      have hb2 : N.factorization 3 ≤ 2 := by
        by_contra hc
        exact hcon 2 27 54 (by decide) (by norm_num) h2
          (by simpa using hdp 3 3 (by omega)) h54
      have hab : ¬ (2 ≤ N.factorization 2 ∧ 2 ≤ N.factorization 3) := by
        rintro ⟨hx, hy⟩
        exact hcon 4 9 36 (by decide) (by norm_num)
          (by simpa using hdp 2 2 hx) (by simpa using hdp 3 2 hy) h36
      have hNeq : N = 2 ^ N.factorization 2 * 3 ^ N.factorization 3 :=
        hstruct _ _ (by decide) hsub23
      generalize hA : N.factorization 2 = a at ha1 ha2 hab hNeq
      generalize hB : N.factorization 3 = b at hb1 hb2 hab hNeq
      interval_cases a <;> interval_cases b <;> rw [hNeq] <;> revert hab <;> decide
    · by_cases b5 : 5 ∈ N.primeFactors
      · -- prime factors `{2, 5}`
        have h2 : (2:ℕ) ∣ N := hd 2 b2
        have h5 : (5:ℕ) ∣ N := hd 5 b5
        have b7 : 7 ∉ N.primeFactors := by
          intro h
          have := key 5 7 b5 h (by decide)
          revert this; decide
        have hsub25 : N.primeFactors ⊆ ({2, 5} : Finset ℕ) := by
          intro r hr
          have h := hsub r hr
          simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
          rcases h with rfl | rfl | rfl | rfl
          exacts [Or.inl rfl, absurd hr b3, Or.inr rfl, absurd hr b7]
        have ha1 : 1 ≤ N.factorization 2 := hposfac 2 b2
        have hc1 : 1 ≤ N.factorization 5 := hposfac 5 b5
        have ha2 : N.factorization 2 ≤ 1 := by
          by_contra hc
          exact hcon 4 5 20 (by decide) (by norm_num)
            (by simpa using hdp 2 2 (by omega)) h5 h20
        have hc2 : N.factorization 5 ≤ 1 := by
          by_contra hc
          exact hcon 2 25 50 (by decide) (by norm_num) h2
            (by simpa using hdp 5 2 (by omega)) h50
        have hNeq : N = 2 ^ N.factorization 2 * 5 ^ N.factorization 5 :=
          hstruct _ _ (by decide) hsub25
        rw [hNeq, le_antisymm ha2 ha1, le_antisymm hc2 hc1]
        decide
      · -- prime factors `{2, 7}`
        have b7 : 7 ∈ N.primeFactors := by
          by_contra b7
          have hs : N.primeFactors ⊆ ({2} : Finset ℕ) := by
            intro r hr
            have h := hsub r hr
            simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
            rcases h with rfl | rfl | rfl | rfl
            exacts [rfl, absurd hr b3, absurd hr b5, absurd hr b7]
          have := Finset.card_le_card hs
          simp only [Finset.card_singleton] at this
          omega
        have h7 : (7:ℕ) ∣ N := hd 7 b7
        have hsub27 : N.primeFactors ⊆ ({2, 7} : Finset ℕ) := by
          intro r hr
          have h := hsub r hr
          simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
          rcases h with rfl | rfl | rfl | rfl
          exacts [Or.inl rfl, absurd hr b3, absurd hr b5, Or.inr rfl]
        have ha1 : 1 ≤ N.factorization 2 := hposfac 2 b2
        have hd1 : 1 ≤ N.factorization 7 := hposfac 7 b7
        have ha2 : N.factorization 2 ≤ 1 := by
          by_contra hc
          exact hcon 4 7 28 (by decide) (by norm_num)
            (by simpa using hdp 2 2 (by omega)) h7 h28
        have hd2 : N.factorization 7 ≤ 1 := by
          by_contra hc
          exact h49 (by simpa using hdp 7 2 (by omega))
        have hNeq : N = 2 ^ N.factorization 2 * 7 ^ N.factorization 7 :=
          hstruct _ _ (by decide) hsub27
        rw [hNeq, le_antisymm ha2 ha1, le_antisymm hd2 hd1]
        decide
  · by_cases b3 : 3 ∈ N.primeFactors
    · by_cases b5 : 5 ∈ N.primeFactors
      · -- prime factors `{3, 5}`
        have h3 : (3:ℕ) ∣ N := hd 3 b3
        have h5 : (5:ℕ) ∣ N := hd 5 b5
        have b7 : 7 ∉ N.primeFactors := by
          intro h
          have := key 5 7 b5 h (by decide)
          revert this; decide
        have hsub35 : N.primeFactors ⊆ ({3, 5} : Finset ℕ) := by
          intro r hr
          have h := hsub r hr
          simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
          rcases h with rfl | rfl | rfl | rfl
          exacts [absurd hr b2, Or.inl rfl, Or.inr rfl, absurd hr b7]
        have hb1 : 1 ≤ N.factorization 3 := hposfac 3 b3
        have hc1 : 1 ≤ N.factorization 5 := hposfac 5 b5
        have hb2 : N.factorization 3 ≤ 1 := by
          by_contra hc
          exact hcon 9 5 45 (by decide) (by norm_num)
            (by simpa using hdp 3 2 (by omega)) h5 h45
        have hc2 : N.factorization 5 ≤ 1 := by
          by_contra hc
          exact hcon 3 25 75 (by decide) (by norm_num) h3
            (by simpa using hdp 5 2 (by omega)) h75
        have hNeq : N = 3 ^ N.factorization 3 * 5 ^ N.factorization 5 :=
          hstruct _ _ (by decide) hsub35
        rw [hNeq, le_antisymm hb2 hb1, le_antisymm hc2 hc1]
        decide
      · -- prime factors `{3, 7}`
        have b7 : 7 ∈ N.primeFactors := by
          by_contra b7
          have hs : N.primeFactors ⊆ ({3} : Finset ℕ) := by
            intro r hr
            have h := hsub r hr
            simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
            rcases h with rfl | rfl | rfl | rfl
            exacts [absurd hr b2, rfl, absurd hr b5, absurd hr b7]
          have := Finset.card_le_card hs
          simp only [Finset.card_singleton] at this
          omega
        have h7 : (7:ℕ) ∣ N := hd 7 b7
        have hsub37 : N.primeFactors ⊆ ({3, 7} : Finset ℕ) := by
          intro r hr
          have h := hsub r hr
          simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
          rcases h with rfl | rfl | rfl | rfl
          exacts [absurd hr b2, Or.inl rfl, absurd hr b5, Or.inr rfl]
        have hb1 : 1 ≤ N.factorization 3 := hposfac 3 b3
        have hd1 : 1 ≤ N.factorization 7 := hposfac 7 b7
        have hb2 : N.factorization 3 ≤ 1 := by
          by_contra hc
          exact hcon 9 7 63 (by decide) (by norm_num)
            (by simpa using hdp 3 2 (by omega)) h7 h63
        have hd2 : N.factorization 7 ≤ 1 := by
          by_contra hc
          exact h49 (by simpa using hdp 7 2 (by omega))
        have hNeq : N = 3 ^ N.factorization 3 * 7 ^ N.factorization 7 :=
          hstruct _ _ (by decide) hsub37
        rw [hNeq, le_antisymm hb2 hb1, le_antisymm hd2 hd1]
        decide
    · -- `2, 3 ∉ primeFactors`: then `5` and `7` both divide `N`, contradicting `35`
      exfalso
      have b5 : 5 ∈ N.primeFactors := by
        by_contra b5
        have hs : N.primeFactors ⊆ ({7} : Finset ℕ) := by
          intro r hr
          have h := hsub r hr
          simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
          rcases h with rfl | rfl | rfl | rfl
          exacts [absurd hr b2, absurd hr b3, absurd hr b5, rfl]
        have := Finset.card_le_card hs
        simp only [Finset.card_singleton] at this
        omega
      have b7 : 7 ∈ N.primeFactors := by
        by_contra b7
        have hs : N.primeFactors ⊆ ({5} : Finset ℕ) := by
          intro r hr
          have h := hsub r hr
          simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
          rcases h with rfl | rfl | rfl | rfl
          exacts [absurd hr b2, absurd hr b3, rfl, absurd hr b7]
        have := Finset.card_le_card hs
        simp only [Finset.card_singleton] at this
        omega
      have := key 5 7 b5 b7 (by decide)
      revert this; decide

/-- **Kenku's cyclic-isogeny degrees with two distinct prime factors**
(PROVEN 2026-07-25 from the twelve nodes above, divisor descent and
`kenku_notPrimePow_arithmetic`; the non-prime-power half of the `X_0`
input): if the cyclic subgroup `⟨g⟩` generated by a geometric point `g` of
an elliptic curve `E/ℚ` has exact order `N ≥ 2` which is NOT a prime power,
and is stable under `Gal(ℚ̄/ℚ)`, then

  `N ∈ {6, 10, 12, 14, 15, 18, 21}`.

`¬ IsPrimePow N` together with `2 ≤ N` says exactly that `N` has at least
two distinct prime factors, and the seven listed values are exactly the
non-prime-powers of the full Mazur–Kenku list
`{1, …, 19, 21, 25, 27, 37, 43, 67, 163}`. So this is the complement of the
four prime-power nodes above, and it carries the bulk of Kenku's 1979–1982
work.

The proof here is only glue: `exists_stable_zmultiples_of_dvd` turns each
divisor of `N` into a Galois-stable cyclic subgroup of that order, which
feeds one of the twelve nodes; `kenku_notPrimePow_arithmetic` then does the
`ℕ` bookkeeping. All the mathematical content sits in the twelve nodes, and
the section note above records what each of them is. Note that Mazur's
prime node is NOT used: the uniform pair node already confines the primes. -/
theorem WeierstrassCurve.notPrimePow_mem_cyclicIsogenyDegrees
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) {N : ℕ} (hN : 2 ≤ N)
    (hpp : ¬ IsPrimePow N) (hg : addOrderOf g = N)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    N ∈ ({6, 10, 12, 14, 15, 18, 21} : Finset ℕ) := by
  have hN0 : N ≠ 0 := by omega
  have hdvd : ∀ d : ℕ, d ∣ N → ∃ g' : (E⁄(AlgebraicClosure ℚ)).Point,
      addOrderOf g' = d ∧
      ∀ σ : Field.absoluteGaloisGroup ℚ,
        ∀ x ∈ AddSubgroup.zmultiples g',
          Affine.Point.map
            (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
            AddSubgroup.zmultiples g' :=
    fun d hd => E.exists_stable_zmultiples_of_dvd g hN0 hd hg hstable
  refine WeierstrassCurve.kenku_notPrimePow_arithmetic N hN hpp ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_
  · intro p q hp hq hne hd
    obtain ⟨g', hg', hs'⟩ := hdvd (p * q) hd
    exact E.not_cyclicIsogeny_prod_two_primes g' hp hq hne hg' hs'
  · intro hd
    obtain ⟨g', hg', hs'⟩ := hdvd 49 hd
    exact E.not_cyclicIsogeny_sq_of_prime_ge_seven g' (p := 7) (by decide) (le_refl 7)
      (by simpa using hg') hs'
  · intro hd
    obtain ⟨g', hg', hs'⟩ := hdvd 20 hd
    exact E.not_cyclicIsogeny_twenty g' hg' hs'
  · intro hd
    obtain ⟨g', hg', hs'⟩ := hdvd 24 hd
    exact E.not_cyclicIsogeny_twentyFour g' hg' hs'
  · intro hd
    obtain ⟨g', hg', hs'⟩ := hdvd 28 hd
    exact E.not_cyclicIsogeny_twentyEight g' hg' hs'
  · intro hd
    obtain ⟨g', hg', hs'⟩ := hdvd 30 hd
    exact E.not_cyclicIsogeny_thirty g' hg' hs'
  · intro hd
    obtain ⟨g', hg', hs'⟩ := hdvd 36 hd
    exact E.not_cyclicIsogeny_thirtySix g' hg' hs'
  · intro hd
    obtain ⟨g', hg', hs'⟩ := hdvd 42 hd
    exact E.not_cyclicIsogeny_fortyTwo g' hg' hs'
  · intro hd
    obtain ⟨g', hg', hs'⟩ := hdvd 45 hd
    exact E.not_cyclicIsogeny_fortyFive g' hg' hs'
  · intro hd
    obtain ⟨g', hg', hs'⟩ := hdvd 50 hd
    exact E.not_cyclicIsogeny_fifty g' hg' hs'
  · intro hd
    obtain ⟨g', hg', hs'⟩ := hdvd 54 hd
    exact E.not_cyclicIsogeny_fiftyFour g' hg' hs'
  · intro hd
    obtain ⟨g', hg', hs'⟩ := hdvd 63 hd
    exact E.not_cyclicIsogeny_sixtyThree g' hg' hs'
  · intro hd
    obtain ⟨g', hg', hs'⟩ := hdvd 75 hd
    exact E.not_cyclicIsogeny_seventyFive g' hg' hs'

/-- **Kenku's composite cyclic-isogeny degrees** (PROVEN 2026-07-25 from
the five nodes above and divisor descent; the composite half of the `X_0`
input): if the cyclic subgroup `⟨g⟩`
generated by a geometric point `g` of an elliptic curve `E/ℚ` has exact
order `N ≥ 20` with `N` NOT prime, and is stable under `Gal(ℚ̄/ℚ)`,
then

  `N ∈ {21, 25, 27}`.

Equivalently: the only non-prime cyclic isogeny degrees over `ℚ` beyond
`19` are `21`, `25` and `27` — the modular curves `X_0(N)` for every
other composite `N ≥ 20` have no non-cuspidal rational point. Kenku's
series of papers (1979–1982), completed in "On the number of
`ℚ`-isomorphism classes of elliptic curves in each `ℚ`-isogeny class"
(J. Number Theory 15, 1982).

The proof here is the arithmetic reassembly described in the section
note above, and it is exhaustive. Write `N` for the order. If `N` is a
prime power `p ^ k` then `k ≥ 2`, since `k = 0` gives `N = 1 < 20` and
`k = 1` contradicts `¬ N.Prime`; and then

* `p ≥ 7`: `p² ∣ N`, so divisor descent plus
  `not_cyclicIsogeny_sq_of_prime_ge_seven` is a contradiction;
* `p = 5`: `k = 2` gives `N = 25`, and `k ≥ 3` gives `125 ∣ N`;
* `p = 3`: `k = 2` gives `N = 9 < 20`, `k = 3` gives `N = 27`, and
  `k ≥ 4` gives `81 ∣ N`;
* `p = 2`: `k ≤ 4` gives `N ≤ 16 < 20`, and `k ≥ 5` gives `32 ∣ N`.

If `N` is not a prime power then `notPrimePow_mem_cyclicIsogenyDegrees`
puts it in `{6, 10, 12, 14, 15, 18, 21}`, of which only `21` is `≥ 20`.
All the mathematical content sits in the five sorried nodes above; the
only step here that is not `Nat` bookkeeping is divisor descent, which
is proven.

Among the eleven critical composite torsion levels this node is what
closes `20`, `24`, `35` and `49`: all four are composite and `≥ 20`,
and none of them is `21`, `25` or `27`.

Sanity-checked with PARI/GP (2026-07-25; untrusted searcher, never a
proof): `ellisomat` over the 20143 nonsingular curves `[a₁,a₂,a₃,a₄,a₆]`
with `a₁, a₃ ∈ {0,1}`, `a₂ ∈ {−1,0,1}`, `a₄, a₆ ∈ [−20,20]` yields the
cyclic isogeny degrees `{1, …, 16, 18, 21, 25, 37}` — the only composite
values `≥ 20` among them are `21` and `25`, and `20`, `24`, `35`, `49`
never occur. -/
theorem WeierstrassCurve.composite_mem_cyclicIsogenyDegrees (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (g : (E⁄(AlgebraicClosure ℚ)).Point) {N : ℕ}
    (hN : 20 ≤ N) (hcomp : ¬ N.Prime) (hg : addOrderOf g = N)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    N ∈ ({21, 25, 27} : Finset ℕ) := by
  have hN0 : N ≠ 0 := by omega
  have hdvd : ∀ d : ℕ, d ∣ N → ∃ g' : (E⁄(AlgebraicClosure ℚ)).Point,
      addOrderOf g' = d ∧
      ∀ σ : Field.absoluteGaloisGroup ℚ,
        ∀ x ∈ AddSubgroup.zmultiples g',
          Affine.Point.map
            (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
            AddSubgroup.zmultiples g' :=
    fun d hd => E.exists_stable_zmultiples_of_dvd g hN0 hd hg hstable
  by_cases hpp : IsPrimePow N
  · obtain ⟨p, k, hp, hk0, hpk⟩ := hpp
    have hpN : p.Prime := Nat.prime_iff.mpr hp
    have hp2 : 2 ≤ p := hpN.two_le
    have hk2 : 2 ≤ k := by
      rcases Nat.lt_or_ge k 2 with h | h
      · have hk1 : k = 1 := by omega
        subst hk1
        rw [pow_one] at hpk
        exact absurd (hpk ▸ hpN) hcomp
      · exact h
    rcases Nat.lt_or_ge p 7 with hp7 | hp7
    · interval_cases p
      · rcases Nat.lt_or_ge k 5 with hk5 | hk5
        · interval_cases k <;> (rw [← hpk] at hN; norm_num at hN)
        · have h32 : (32 : ℕ) ∣ N := by
            rw [← hpk, show (32 : ℕ) = 2 ^ 5 by norm_num]
            exact pow_dvd_pow 2 hk5
          obtain ⟨g', hg', hs'⟩ := hdvd 32 h32
          exact (E.not_cyclicIsogeny_thirtyTwo g' hg' hs').elim
      · rcases Nat.lt_or_ge k 4 with hk4 | hk4
        · interval_cases k
          · rw [← hpk] at hN; norm_num at hN
          · rw [← hpk]; decide
        · have h81 : (81 : ℕ) ∣ N := by
            rw [← hpk, show (81 : ℕ) = 3 ^ 4 by norm_num]
            exact pow_dvd_pow 3 hk4
          obtain ⟨g', hg', hs'⟩ := hdvd 81 h81
          exact (E.not_cyclicIsogeny_eightyOne g' hg' hs').elim
      · rcases hpN.eq_one_or_self_of_dvd 2 ⟨2, rfl⟩ with h | h <;> omega
      · rcases Nat.lt_or_ge k 3 with hk3 | hk3
        · interval_cases k
          · rw [← hpk]; decide
        · have h125 : (125 : ℕ) ∣ N := by
            rw [← hpk, show (125 : ℕ) = 5 ^ 3 by norm_num]
            exact pow_dvd_pow 5 hk3
          obtain ⟨g', hg', hs'⟩ := hdvd 125 h125
          exact (E.not_cyclicIsogeny_oneHundredTwentyFive g' hg' hs').elim
      · rcases hpN.eq_one_or_self_of_dvd 2 ⟨3, rfl⟩ with h | h <;> omega
    · have hsq : p ^ 2 ∣ N := by rw [← hpk]; exact pow_dvd_pow p hk2
      obtain ⟨g', hg', hs'⟩ := hdvd (p ^ 2) hsq
      exact (E.not_cyclicIsogeny_sq_of_prime_ge_seven g' hpN hp7 hg' hs').elim
  · have h := E.notPrimePow_mem_cyclicIsogenyDegrees g (by omega) hpp hg hstable
    fin_cases h <;> revert hN <;> decide

/-- **The rational cyclic-isogeny degrees over `ℚ`** (PROVEN 2026-07-25
from the two nodes above; the `X_0` input, Mazur 1978 and Kenku
1979–1982): if the cyclic subgroup `⟨g⟩` generated by a geometric point
`g` of an elliptic curve `E/ℚ` has exact finite order `N` and is stable
under `Gal(ℚ̄/ℚ)`, then

  `N ∈ {1, …, 19, 21, 25, 27, 37, 43, 67, 163}`.

This is the classical determination of the non-cuspidal rational points
of the modular curves `X_0(N)`: a Galois-stable cyclic subgroup of
order `N` is the kernel of a cyclic `N`-isogeny `E → E/⟨g⟩` defined over
`ℚ` (Vélu), and conversely, so the listed `N` are exactly those for
which `X_0(N)(ℚ)` contains a non-cuspidal point.

The proof here is only the bookkeeping that reassembles the list from
its two halves, and it is genuinely exhaustive in three ranges: `N`
prime is Mazur's node (all twelve of whose values are in the list, so
no size hypothesis is needed); `N` non-prime with `N < 20` needs no
input at all, since `0 < N < 20` already forces `N ∈ {1, …, 19}`; and
`N` non-prime with `N ≥ 20` is Kenku's node. The mathematical content
is entirely in the two sorried nodes.

Among the eleven critical composite torsion levels this closes exactly
`20`, `24`, `35` and `49`, the four that are absent from the list, and
all four are PROVEN from it below. -/
theorem WeierstrassCurve.mem_cyclicIsogenyDegrees (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (g : (E⁄(AlgebraicClosure ℚ)).Point) {N : ℕ}
    (hN : 0 < N) (hg : addOrderOf g = N)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    N ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
      21, 25, 27, 37, 43, 67, 163} : Finset ℕ) := by
  by_cases hp : N.Prime
  · have h := E.prime_mem_cyclicIsogenyDegrees g hp hg hstable
    fin_cases h <;> decide
  · rcases lt_or_ge N 20 with h20 | h20
    · interval_cases N <;> decide
    · have h := E.composite_mem_cyclicIsogenyDegrees g h20 hp hg hstable
      fin_cases h <;> decide

/-- **From a rational point to a Galois-stable cyclic subgroup**
(PROVEN 2026-07-25): a rational point `Q` of exact order `n`
base-changes to a geometric point `g` of the same order whose cyclic
subgroup `⟨g⟩` is stable under `Gal(ℚ̄/ℚ)` — which is exactly the datum
of a non-cuspidal rational point of `X_0(n)`.

Both halves are formal: `Affine.Point.map` along an injective algebra
map preserves the additive order (`Affine.Point.map_injective`), and
`Affine.Point.map_baseChange` says every `ℚ`-algebra endomorphism of
`ℚ̄` fixes the base change of a rational point, so `σ` sends `k • g` to
`k • g` and `⟨g⟩` is in fact pointwise Galois-FIXED.

This is the `X_1 → X_0` bridge for the whole section. It returns the
witness `g`, so it serves both `mem_cyclicIsogenyDegrees_of_addOrderOf`
just below — which needs only the resulting membership in Kenku's list
— and the level-`27` `j`-determination further down, which needs `g`
itself because being IN Kenku's list is no contradiction there.

INSTANCE-DIAMOND NOTE (repaired 2026-07-25 — do NOT "simplify" the
`convert` back into a `rw`): `CommRing (AlgebraicClosure ℚ)` has two
syntactically distinct terms in this file's environment,
`AlgebraicClosure.instCommRing ℚ` and
`Field.toCommRing _ (AlgebraicClosure.instField ℚ)`.  They are defeq,
but the statement mixes them: the `⁄`-notation in the binder
`g : (E⁄(AlgebraicClosure ℚ)).Point` synthesises `CommRing` directly
and gets the former, while mathlib's `Affine.Point.map` /
`Affine.Point.baseChange` take `[Field K]` and build the latter.  So
`rw [Affine.Point.map_baseChange …]` cannot key-match its own LHS
against this goal — it fails with "did not find an occurrence" on a
pattern that pretty-prints IDENTICALLY to the target, which is what
makes the failure so confusing.  `convert … using 2` discharges the
two instance positions by defeq and leaves exactly the intended
equation.  `simpa only [Affine.Point.map_baseChange]` does NOT work
here, for the same keyed-matching reason. -/
theorem WeierstrassCurve.exists_stable_cyclic_subgroup_of_rational_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {n : ℕ}
    (Q : (E⁄ℚ).Point) (hQ : addOrderOf Q = n) :
    ∃ g : (E⁄(AlgebraicClosure ℚ)).Point, addOrderOf g = n ∧
      ∀ σ : Field.absoluteGaloisGroup ℚ,
        ∀ x ∈ AddSubgroup.zmultiples g,
          Affine.Point.map
            (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
            AddSubgroup.zmultiples g := by
  refine ⟨Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) Q, ?_, ?_⟩
  · rw [← hQ]
    exact addOrderOf_injective _
      (Affine.Point.map_injective (f := Algebra.ofId ℚ (AlgebraicClosure ℚ))) Q
  · intro σ x hx
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    -- REPAIRED 2026-07-25 (flt-lean-88, while verifying an unrelated leaf in
    -- `Modularity/Patching.lean`, which imports this module).  The previous
    -- `rw [map_zsmul, Affine.Point.map_baseChange …]` was failing on `main`
    -- with "did not find an occurrence of the pattern" on a pattern that is
    -- VISIBLY present in the goal: mathlib's `Affine.Point.map_baseChange`
    -- elaborates its `Point.map` over the curve `W'⁄F` (base-changed to the
    -- intermediate field), whereas the goal here carries `Point.map` over `E`
    -- itself.  Those are DEFEQ but not syntactically equal, so neither `rw`
    -- nor `simp only` can match — `simp only [Affine.Point.map_baseChange]`
    -- reports the lemma as an unused argument.  Restating the equation with
    -- the goal's own elaboration and letting `exact` bridge the two by
    -- definitional unfolding is what closes it.  Nothing about the statement
    -- or the mathematics changed; this was a hard error blocking the whole
    -- downstream cone.  THREE agents diagnosed this independently; one built a
    -- two-way reproduction in a minimal module (old line fails, this one
    -- succeeds), and located the mismatch in the `IsScalarTower`/`Algebra`
    -- arguments that `rw`'s syntactic matching will not cross.
    have hfix : Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom
          (Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) Q)
        = Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) Q :=
      Affine.Point.map_baseChange
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom Q
    rw [map_zsmul, hfix]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples _) k

/-- **A rational torsion point has Kenku degree** (PROVEN 2026-07-25):
a rational point `Q` of exact order `N > 0` generates a cyclic subgroup
of order `N` in `E(ℚ̄)` all of whose elements are base changes of
rational points, hence pointwise Galois-FIXED and in particular
Galois-stable; so `N` lies in Kenku's list of cyclic isogeny degrees.
Immediate from the bridge above. -/
lemma WeierstrassCurve.mem_cyclicIsogenyDegrees_of_addOrderOf
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (Q : (E⁄ℚ).Point) {N : ℕ}
    (hN : 0 < N) (hQ : addOrderOf Q = N) :
    N ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
      21, 25, 27, 37, 43, 67, 163} : Finset ℕ) := by
  obtain ⟨g, hgord, hstable⟩ :=
    E.exists_stable_cyclic_subgroup_of_rational_point Q hQ
  exact E.mem_cyclicIsogenyDegrees g hN hgord hstable

/-!
##### The eight prime levels `≥ 11`, one node each (2026-07-25)

`no_prime_torsion_ge_eleven` — Mazur, "Modular curves and the Eisenstein
ideal" (Publ. Math. IHÉS 47, 1977), Thm 7 — used to be a single bare
`sorry` ranging over infinitely many primes. It is PROVEN below from the
`X_0` input `mem_cyclicIsogenyDegrees` together with EIGHT per-level
nodes, in exactly the shape `no_composite_torsion_order` already has:
one canonical citable theorem doing the uniform work, one node per
surviving level, and the passage between them proven rather than
asserted.

THE CUT. A rational point of order `ℓ` generates a rational — hence
pointwise Galois-fixed, hence stable — cyclic subgroup of order `ℓ`,
i.e. a rational cyclic `ℓ`-isogeny; that step is the already-PROVEN
`mem_cyclicIsogenyDegrees_of_addOrderOf` just above. So `ℓ` lies in
Kenku's list `{1, …, 19, 21, 25, 27, 37, 43, 67, 163}`, and the two
hypotheses on `ℓ` cut it down with no further input: `11 ≤ ℓ` deletes
`1, …, 10`, and primality deletes `12, 14, 15, 16, 18, 21, 25, 27`.
What is left is exactly

  `ℓ ∈ {11, 13, 17, 19, 37, 43, 67, 163}`,

the primes `≥ 11` of Mazur's isogeny theorem (`prime_mem_cyclicIsogenyDegrees`,
Mazur 1978, Thm 1). Every other prime `ℓ ≥ 11` — infinitely many — is
therefore discharged outright, where before it was covered by an
assertion.

WHERE THE `X_0` SHORTCUT STOPS, AND WHY THAT IS NOT A DEFECT OF THE
CUT. By the criterion stated once in the section note above, the
shortcut is available at a level exactly when that level is ABSENT from
Kenku's list. All eight surviving primes are PRESENT in it, so at each
of them a rational cyclic `ℓ`-isogeny genuinely exists and is no
contradiction at all; only the finer `X_1(ℓ)` statement excludes the
point. Explicit witnesses, all confirmed with PARI/GP `ellisomat`
(untrusted searcher, never a proof — each was checked to have cyclic
isogeny degree set exactly `{1, ℓ}` unless noted):

* `ℓ = 11`: the three non-cuspidal rational points of `X_0(11)`,
  `j = −32768 = −2¹⁵` (CM by discriminant `−11`), `j = −121`,
  `j = −24729001`;
* `ℓ = 13`: `X_0(13)` has genus `0`, so infinitely many; a concrete
  model is `y² = x³ + 6x − 8`, of conductor `20736`;
* `ℓ = 17`: `j = −17 · 373³ / 2¹⁷` and `j = −17² · 101³ / 2`;
* `ℓ = 37`: `j = −7 · 11³`;
* `ℓ = 19, 43, 67, 163`: the class-number-one CM `j`-invariants of
  discriminant `−ℓ`, namely `−884736`, `−884736000`, `−147197952000`
  and `−262537412640768000`.

GENERA of `X_1(ℓ)`, from `g = (ℓ − 5)(ℓ − 7) / 24` for prime `ℓ ≥ 5`
(recomputed 2026-07-25): `11 ↦ 1`, `13 ↦ 2`, `17 ↦ 5`, `19 ↦ 7`,
`37 ↦ 40`, `43 ↦ 57`, `67 ↦ 155`, `163 ↦ 1027`. The `11 ↦ 1` and
`37 ↦ 40` values agree with the figures already recorded elsewhere in
this file.

SUPERSEDED CLAIMS ELSEWHERE IN THIS FILE, RECONCILED HERE (both were
correct as statements about CLOSING the node, and both are now too
strong as statements about REDUCING it):

* `prime_mem_cyclicIsogenyDegrees`'s docstring says the `X_0` node and
  this one are stated separately because "neither implies the other …
  `X_1(ℓ) → X_0(ℓ)` runs the wrong way to transfer the conclusion".
  The map runs perfectly well in the direction actually used — a
  rational POINT of order `ℓ` does give a rational SUBGROUP of order
  `ℓ` — and that is exactly what the cut below exploits. What does not
  transfer is emptiness of the conclusion: `X_0(ℓ)(ℚ)` has
  non-cuspidal points at all eight surviving levels, so the `X_0` node
  reduces the family to eight levels and cannot close any of them.
  Both nodes are still needed and neither is redundant.
* the old docstring of this theorem listed "Mazur's isogeny theorem"
  among the shortcuts that FAIL, on the same ground — that it "would
  only reduce this uniform statement to those eight individual levels".
  That reduction is precisely what is carried out below; it was
  correctly judged not to be a proof, and wrongly left unperformed.

NON-CIRCULARITY. Routing Thm 7 through Thm 1 is a legitimate reduction
and not a circle: Mazur's isogeny theorem is not deduced from the
torsion theorem — both rest on the Eisenstein-ideal descent on `J_0(ℓ)`
developed in the 1977 paper. The reduction does make the shared
dependence visible in the tree, which is the same reason the `X_0` node
was split into its two citations above.

WHAT THIS DOES NOT BUY. It does not make any level easier: all eight
nodes are IRREDUCIBLE at this mathlib pin, and nothing here is
dispatchable until modular curves exist in the development. Two of the
eight have classical pre-Mazur proofs (`ℓ = 11`: Billing–Mahler 1940;
`ℓ = 13`: Mazur–Tate 1973), both of them Mordell–Weil computations on a
genus-`1` resp. genus-`2` curve; the remaining six are Mazur 1977,
Thm 7 itself, and for `ℓ = 37, 43, 67, 163` the genus is far beyond any
explicit descent.

MISSING MACHINERY, IN DEPENDENCY ORDER (none of it exists here, and
mathlib has none of it either):

1. `X_1(N)` and `X_0(N)` as smooth projective curves over `ℚ`, with the
   moduli interpretation — a non-cuspidal point of `X_1(N)(ℚ)`
   corresponds to a pair `(E, P)` with `P ∈ E(ℚ)` of exact order `N`,
   up to `ℚ`-isomorphism. This is the piece that would let any of the
   eight nodes even be RESTATED geometrically; everything below needs
   it first.
2. The Jacobians `J_0(N)`, `J_1(N)` as abelian varieties over `ℚ`, and
   the Hecke algebra acting on them.
3. Mordell–Weil for abelian varieties over `ℚ`. Mathlib has no
   Mordell–Weil theorem at all, not even for elliptic curves, so even
   the two classical levels `11` and `13` are blocked here.
4. The Eisenstein ideal, the Eisenstein quotient of `J_0(ℓ)`, and the
   theorem that it has Mordell–Weil rank `0` over `ℚ`.
5. Néron models over `ℤ` and the formal-immersion criterion, which is
   how the rank-`0` statement is turned into "the rational points are
   cusps".

The elementary route stays closed at every one of the eight, for the
reason already recorded: rational torsion injects into `Ẽ(𝔽_p)` at a
prime `p` of good reduction (odd `p`, or any `p` for odd torsion), so
`ℓ ≤ p + 1 + 2√p` there, which only forces bad reduction at the small
primes and is a lower bound on the conductor, never a contradiction.

FIRST BRICK BUILT (2026-07-25). Item 1 of the missing-machinery list is
not reachable in one step, but its elementary prerequisite is, and it is
now PROVEN here: `exists_tateNormalForm`, the Tate normal form for a
point of order `≥ 4`. Consequently each of the eight nodes is stated in
the coordinates the literature uses — about the explicit family
`tateNormalForm b c` and the origin, i.e. about a plane model of
`X_1(ℓ)` — and the general per-level statements `no_torsion_order_ℓ` are
PROVEN from them. Nothing was assumed to do this and no level got
easier; what changed is that the reduction to standard coordinates is
now checked by the compiler instead of being left implicit. See the
Tate-normal-form section note immediately below.
-/

/-!
##### Tate normal form: the coordinates every `X_1(n)` computation starts in

The eight nodes below are stated in the coordinates the literature
actually uses. The passage into those coordinates is NOT assumed: it is
the PROVEN theorem `exists_tateNormalForm` in this section, which is new
here and has no mathlib counterpart.

An elliptic curve over `ℚ` with a rational point `P` of order `≥ 4` is
`ℚ`-isomorphic to

  `y² + (1 − c) x y − b y = x³ − b x²`,

by an isomorphism carrying `P` to `(0, 0)`. The derivation is three
admissible changes of variables, and each of the two divisions it
performs is licensed by one of the two order hypotheses — which is
exactly why `4` is the threshold:

* translate `P` to the origin (`r = X`, `t = Y`); the constant term
  `a₆` dies because `P` lies on the curve;
* shear by `s` to kill `a₄`. The shear needed is `s = A / a₃'` with
  `a₃' = a₃ + X a₁ + 2Y`, and `a₃' ≠ 0` is precisely `2P ≠ 0` — it is
  the quantity `y − negY(x, y)` at `P`, whose vanishing characterises
  `2`-torsion;
* rescale by `u = a₃'/a₂'` to force `a₂ = a₃`. Here `a₂' ≠ 0` is
  precisely `3P ≠ 0`: once `a₄ = a₆ = 0`, the tangent at the origin is
  `y = 0`, which meets `x³ + a₂' x² = 0` in the third point `x = −a₂'`,
  so `a₂' = 0` says the origin is a flex, i.e. a point of order `3`.
  That direction is the PROVEN `three_nsmul_origin_eq_zero` below, and
  it is the only place any point arithmetic is needed.

The transport of the Mordell–Weil group along the changes of variables
is `Point.equivVariableChange` from the repo's mathlib shim; everything
stays over `ℚ`, so no Galois bookkeeping is required (unlike the
two-torsion normal form later in this file, which needs `ℚ̄`).

WHAT THIS BUYS AND WHAT IT DOES NOT. It reduces each level `ℓ` from a
statement about ALL elliptic curves to a statement about the explicit
two-parameter family `tateNormalForm b c` and the single point `(0,0)` —
i.e. to a plane model of `X_1(ℓ)` in the `(b, c)`-coordinates, which is
where every classical treatment begins. It does NOT settle any level:
what remains at each is the Diophantine content, and that still needs
the missing machinery listed in the section note above. The same
theorem serves levels `21, 25, 27` and the composite levels, none of
which are touched here.
-/

namespace WeierstrassCurve

/-- **Tate normal form** `y² + (1 − c) x y − b y = x³ − b x²`, the
standard plane model in which a point of order `≥ 4` sits at the origin.
The `(b, c)`-plane is the standard affine model of `X_1(n)` once the
order-`n` condition on `(0,0)` is imposed. -/
def tateNormalForm (b c : ℚ) : WeierstrassCurve ℚ := ⟨1 - c, -b, -b, 0, 0⟩

/-- **The origin is a flex when `a₂` vanishes** (PROVEN): on a curve
`y² + a₁ x y + a₃ y = x³ + a₂ x² + a₄ x` with `a₂ = a₄ = 0` and
`a₃ ≠ 0`, the origin is a point of order dividing `3`.

`a₄ = 0` makes the tangent slope at `(0,0)` equal `a₄/a₃ = 0`, so the
tangent is the line `y = 0`; it meets the curve where `x³ + a₂ x² = 0`,
which with `a₂ = 0` is `x³ = 0` — a triple contact. Concretely the
doubling formulas give `addX = −a₂ = 0` and `negAddY = 0`, so
`P + P = −P`. The hypothesis `a₃ ≠ 0` is what makes the tangent
non-vertical, i.e. `P` not `2`-torsion. -/
lemma three_nsmul_origin_eq_zero (V : WeierstrassCurve ℚ)
    (h2 : V.a₂ = 0) (h4 : V.a₄ = 0) (h3 : V.a₃ ≠ 0)
    (h00 : V.toAffine.Nonsingular 0 0) :
    Affine.Point.some 0 0 h00 + Affine.Point.some 0 0 h00 +
      Affine.Point.some 0 0 h00 = 0 := by
  have hne : (0 : ℚ) ≠ V.toAffine.negY 0 0 := by
    simp only [Affine.negY]
    intro h
    exact h3 (by linarith)
  have hslope : V.toAffine.slope 0 0 0 0 = 0 := by
    rw [Affine.slope_of_Y_ne rfl hne]
    simp only [Affine.negY, h2, h4]
    ring_nf
  have key : Affine.Point.some 0 0 h00 + Affine.Point.some 0 0 h00 =
      -Affine.Point.some 0 0 h00 := by
    rw [Affine.Point.add_self_of_Y_ne' hne]
    congr 1
    refine Affine.Point.some_eq_some V ?_ ?_
    · simp only [Affine.addX, hslope, h2]; ring
    · simp only [Affine.negAddY, Affine.addX, hslope, h2]; ring
  rw [key, neg_add_cancel]

/-- **Tate normal form for a point of order `≥ 4`** (PROVEN 2026-07-25;
no mathlib counterpart): an elliptic curve `W` over `ℚ` carrying a
rational point `P` with `4 ≤ addOrderOf P` is `ℚ`-isomorphic to
`tateNormalForm b c` for some `b, c ∈ ℚ`, by an isomorphism of
Mordell–Weil groups carrying `P` to `(0, 0)`.

See the section note above for the derivation and for which order
hypothesis licenses which division. Silverman ATAEC / Husemöller
"Elliptic Curves" Ch. 4; the form is due to Tate. -/
theorem exists_tateNormalForm (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (P : W.toAffine.Point) (h4 : 4 ≤ addOrderOf P) :
    ∃ (b c : ℚ) (_ : (tateNormalForm b c).IsElliptic)
      (h00 : (tateNormalForm b c).toAffine.Nonsingular 0 0)
      (Ψ : W.toAffine.Point ≃+ (tateNormalForm b c).toAffine.Point),
      Ψ P = Affine.Point.some 0 0 h00 := by
  have hPP : P + P ≠ 0 := by
    intro h
    rw [← two_nsmul] at h
    have := Nat.le_of_dvd (by norm_num) (addOrderOf_dvd_of_nsmul_eq_zero h)
    omega
  have hPPP : P + P + P ≠ 0 := by
    intro h
    have h3 : (3 : ℕ) • P = 0 := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, two_nsmul, one_nsmul]; exact h
    have := Nat.le_of_dvd (by norm_num) (addOrderOf_dvd_of_nsmul_eq_zero h3)
    omega
  rcases P with _ | ⟨X, Y, hns⟩
  · exact absurd (by simp [← Affine.Point.zero_def]) hPP
  -- `2P ≠ 0` is exactly nonvanishing of `a₃'`, the tangent denominator at `P`.
  have hY2 : W.a₃ + X * W.a₁ + 2 * Y ≠ 0 := by
    intro h0
    refine hPP (Affine.Point.add_of_Y_eq rfl ?_)
    simp only [Affine.negY]
    linarith
  set s : ℚ := (W.a₄ + 2 * X * W.a₂ - Y * W.a₁ + 3 * X ^ 2) / (W.a₃ + X * W.a₁ + 2 * Y)
    with hs
  have hs4 : s * (W.a₃ + X * W.a₁ + 2 * Y) =
      W.a₄ + 2 * X * W.a₂ - Y * W.a₁ + 3 * X ^ 2 := div_mul_cancel₀ _ hY2
  set C₁ : VariableChange ℚ := ⟨1, X, s, Y⟩ with hC₁
  set W₁ : WeierstrassCurve ℚ := C₁ • W with hW₁
  have hE : W.toAffine.Equation X Y := hns.1
  have h₁6 : W₁.a₆ = 0 := by
    rw [hW₁, variableChange_a₆, hC₁]
    rw [Affine.equation_iff] at hE
    simp only [Units.val_one, inv_one, one_pow, one_mul]
    linarith [hE]
  have h₁4 : W₁.a₄ = 0 := by
    rw [hW₁, variableChange_a₄, hC₁]
    simp only [Units.val_one, inv_one, one_pow, one_mul]
    linear_combination -hs4
  have h₁3 : W₁.a₃ = W.a₃ + X * W.a₁ + 2 * Y := by
    rw [hW₁, variableChange_a₃, hC₁]
    simp only [Units.val_one, inv_one, one_pow, one_mul]
  have h₁3ne : W₁.a₃ ≠ 0 := by rw [h₁3]; exact hY2
  have h₀₁ : W₁.toAffine.Nonsingular 0 0 :=
    Affine.equation_iff_nonsingular.mp ((Affine.equation_zero (W := W₁)).mpr h₁6)
  have hΨ₁ : (Point.equivVariableChange W C₁).symm (Affine.Point.some X Y hns) =
      Affine.Point.some 0 0 h₀₁ := by
    rw [AddEquiv.symm_apply_eq, Point.equivVariableChange_some]
    exact (Affine.Point.some_eq_some W (by simp [hC₁]) (by simp [hC₁])).symm
  -- `3P ≠ 0` is exactly nonvanishing of `a₂'`: otherwise the origin is a flex.
  have h₁2ne : W₁.a₂ ≠ 0 := by
    intro h0
    refine hPPP ?_
    have h3 := three_nsmul_origin_eq_zero W₁ h0 h₁4 h₁3ne h₀₁
    have hmap := congrArg (Point.equivVariableChange W C₁) h3
    rw [map_add, map_add, ← hΨ₁] at hmap
    simpa [AddEquiv.apply_symm_apply] using hmap
  set u : ℚˣ := Units.mk0 (W₁.a₃ / W₁.a₂) (div_ne_zero h₁3ne h₁2ne) with hu
  set C₂ : VariableChange ℚ := ⟨u, 0, 0, 0⟩ with hC₂
  set W₂ : WeierstrassCurve ℚ := C₂ • W₁ with hW₂
  set b : ℚ := -(W₁.a₂ ^ 3 / W₁.a₃ ^ 2) with hb
  set c : ℚ := 1 - (W₁.a₂ / W₁.a₃) * W₁.a₁ with hc
  have huinv : ((u : ℚ))⁻¹ = W₁.a₂ / W₁.a₃ := by
    rw [hu]
    simp only [Units.val_mk0]
    rw [inv_div]
  have hEq : W₂ = tateNormalForm b c := by
    refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
    · rw [hW₂, variableChange_a₁, hC₂, tateNormalForm, hc]
      simp only [Units.val_inv_eq_inv_val, huinv]
      ring
    · rw [hW₂, variableChange_a₂, hC₂, tateNormalForm, hb]
      simp only [Units.val_inv_eq_inv_val, huinv]
      field_simp
      ring
    · rw [hW₂, variableChange_a₃, hC₂, tateNormalForm, hb]
      simp only [Units.val_inv_eq_inv_val, huinv]
      field_simp
      ring
    · rw [hW₂, variableChange_a₄, hC₂, tateNormalForm, h₁4]
      simp
    · rw [hW₂, variableChange_a₆, hC₂, tateNormalForm, h₁6]
      simp
  have h₀₂ : W₂.toAffine.Nonsingular 0 0 := by
    refine Affine.equation_iff_nonsingular.mp ((Affine.equation_zero (W := W₂)).mpr ?_)
    rw [hW₂, variableChange_a₆, hC₂, h₁6]
    simp
  have hΨ₂ : (Point.equivVariableChange W₁ C₂).symm (Affine.Point.some 0 0 h₀₁) =
      Affine.Point.some 0 0 h₀₂ := by
    rw [AddEquiv.symm_apply_eq, Point.equivVariableChange_some]
    exact (Affine.Point.some_eq_some W₁ (by simp [hC₂]) (by simp [hC₂])).symm
  refine ⟨b, c, hEq ▸ (inferInstance : W₂.IsElliptic), hEq ▸ h₀₂,
    ((Point.equivVariableChange W C₁).symm.trans
      ((Point.equivVariableChange W₁ C₂).symm.trans (Point.equivOfEq hEq))), ?_⟩
  rw [AddEquiv.trans_apply, AddEquiv.trans_apply, hΨ₁, hΨ₂, Point.equivOfEq_some]

/-- **Passage to Tate coordinates at a level `ℓ ≥ 11`** (PROVEN): if the
origin of every `tateNormalForm b c` fails to have order `ℓ`, then no
rational point of any elliptic curve over `ℚ` has order `ℓ`. This is
`exists_tateNormalForm` packaged for the eight nodes below; `4 ≤ ℓ` is
supplied by `11 ≤ ℓ`. -/
lemma no_torsion_order_of_tateNormalForm {ℓ : ℕ} (h4 : 4 ≤ ℓ)
    (h : ∀ (b c : ℚ) (_ : (tateNormalForm b c).IsElliptic)
      (h00 : (tateNormalForm b c).toAffine.Nonsingular 0 0),
        addOrderOf (Affine.Point.some 0 0 h00) ≠ ℓ)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (Q : (E⁄ℚ).Point) :
    addOrderOf Q ≠ ℓ := by
  intro hQ
  haveI : (E⁄ℚ).IsElliptic := inferInstanceAs ((E.map (algebraMap ℚ ℚ)).IsElliptic)
  obtain ⟨b, c, hell, h00, Ψ, hΨ⟩ := exists_tateNormalForm (E⁄ℚ) Q (by omega)
  exact h b c hell h00 (by rw [← hΨ, AddEquiv.addOrderOf_eq]; exact hQ)

end WeierstrassCurve

/-- **No rational point of order `11`** (sorry node — IRREDUCIBLE
literature citation, audited 2026-07-25): `X_1(11)` is the elliptic
curve of genus `1` whose Mordell–Weil group over `ℚ` is `ℤ/5`, and all
five of its rational points are cusps. Billing–Mahler, "On exceptional
points on cubic curves" (J. London Math. Soc. 15, 1940); subsumed in
Mazur 1977, Thm 7.

The `X_0` shortcut of `mem_cyclicIsogenyDegrees` is NOT available here:
`11` is in Kenku's list, and `X_0(11)` has three non-cuspidal rational
points, `j = −32768`, `−121`, `−24729001` (PARI/GP `ellisomat`,
untrusted searcher). So a rational cyclic `11`-isogeny is no
contradiction, and only the finer `X_1(11)` statement excludes the
point. A formal proof needs `X_1(11)` as an arithmetic curve together
with a rank-`0` Mordell–Weil computation; neither exists here. 
STATED IN TATE COORDINATES (2026-07-25). The general form of this
level — no rational point of order `11` on ANY elliptic curve over
`ℚ` — is `no_torsion_order_11` just below, and is PROVEN from this
node. Here the curve is the explicit two-parameter family
`tateNormalForm b c` and the point is the origin, so this node IS the
plane model of `X_1(11)` in the `(b, c)`-coordinates rather than a
statement quantified over all curves. The passage between the two is
the PROVEN `exists_tateNormalForm`; everything above about genus,
witnesses and citation is unchanged by the restatement.
-/
theorem WeierstrassCurve.tateNormalForm_origin_order_ne_11 (b c : ℚ)
    [(WeierstrassCurve.tateNormalForm b c).IsElliptic]
    (h00 : (WeierstrassCurve.tateNormalForm b c).toAffine.Nonsingular 0 0) :
    addOrderOf (Affine.Point.some 0 0 h00) ≠ 11 :=
  sorry

/-- **No rational point of order `11`** (PROVEN 2026-07-25 from the
Tate-coordinate node above through `no_torsion_order_of_tateNormalForm`):
a point of order `11 ≥ 4` puts its curve in Tate normal form at the
origin, so the general statement follows from the one about the
explicit family. All the mathematical content is in the node above,
whose docstring carries this level's citation and audit. -/
theorem WeierstrassCurve.no_torsion_order_11 (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (Q : (E⁄ℚ).Point) : addOrderOf Q ≠ 11 :=
  WeierstrassCurve.no_torsion_order_of_tateNormalForm (by norm_num)
    (fun b c hell h00 =>
      @WeierstrassCurve.tateNormalForm_origin_order_ne_11 b c hell h00) E Q

/-- **No rational point of order `13`** (sorry node — IRREDUCIBLE
literature citation, audited 2026-07-25): `X_1(13)` has genus `2` and no
non-cuspidal rational point. Mazur–Tate, "Points of order 13 on elliptic
curves" (Invent. Math. 22, 1973); subsumed in Mazur 1977, Thm 7.

The `X_0` shortcut is NOT available: `13` is in Kenku's list, and
`X_0(13)` has genus `0`, so rational cyclic `13`-isogenies exist in
abundance — `y² = x³ + 6x − 8`, of conductor `20736`, is one (PARI/GP
`ellisomat`, untrusted searcher). A formal proof needs the rational
points of a genus-`2` curve, i.e. Mordell–Weil on its Jacobian plus a
Chabauty-style argument. 
STATED IN TATE COORDINATES (2026-07-25). The general form of this
level — no rational point of order `13` on ANY elliptic curve over
`ℚ` — is `no_torsion_order_13` just below, and is PROVEN from this
node. Here the curve is the explicit two-parameter family
`tateNormalForm b c` and the point is the origin, so this node IS the
plane model of `X_1(13)` in the `(b, c)`-coordinates rather than a
statement quantified over all curves. The passage between the two is
the PROVEN `exists_tateNormalForm`; everything above about genus,
witnesses and citation is unchanged by the restatement.
-/
theorem WeierstrassCurve.tateNormalForm_origin_order_ne_13 (b c : ℚ)
    [(WeierstrassCurve.tateNormalForm b c).IsElliptic]
    (h00 : (WeierstrassCurve.tateNormalForm b c).toAffine.Nonsingular 0 0) :
    addOrderOf (Affine.Point.some 0 0 h00) ≠ 13 :=
  sorry

/-- **No rational point of order `13`** (PROVEN 2026-07-25 from the
Tate-coordinate node above through `no_torsion_order_of_tateNormalForm`):
a point of order `13 ≥ 4` puts its curve in Tate normal form at the
origin, so the general statement follows from the one about the
explicit family. All the mathematical content is in the node above,
whose docstring carries this level's citation and audit. -/
theorem WeierstrassCurve.no_torsion_order_13 (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (Q : (E⁄ℚ).Point) : addOrderOf Q ≠ 13 :=
  WeierstrassCurve.no_torsion_order_of_tateNormalForm (by norm_num)
    (fun b c hell h00 =>
      @WeierstrassCurve.tateNormalForm_origin_order_ne_13 b c hell h00) E Q

/-- **No rational point of order `17`** (sorry node — IRREDUCIBLE
literature citation, audited 2026-07-25): `X_1(17)` has genus `5` and no
non-cuspidal rational point (Mazur 1977, Thm 7).

The `X_0` shortcut is NOT available: `17` is in Kenku's list, and
`X_0(17)` — a genus-`1` curve of Mordell–Weil rank `0` — has
non-cuspidal rational points, `j = −17 · 373³ / 2¹⁷` and
`j = −17² · 101³ / 2` (PARI/GP `ellisomat`, untrusted searcher), so a
rational cyclic `17`-isogeny is no contradiction. 
STATED IN TATE COORDINATES (2026-07-25). The general form of this
level — no rational point of order `17` on ANY elliptic curve over
`ℚ` — is `no_torsion_order_17` just below, and is PROVEN from this
node. Here the curve is the explicit two-parameter family
`tateNormalForm b c` and the point is the origin, so this node IS the
plane model of `X_1(17)` in the `(b, c)`-coordinates rather than a
statement quantified over all curves. The passage between the two is
the PROVEN `exists_tateNormalForm`; everything above about genus,
witnesses and citation is unchanged by the restatement.
-/
theorem WeierstrassCurve.tateNormalForm_origin_order_ne_17 (b c : ℚ)
    [(WeierstrassCurve.tateNormalForm b c).IsElliptic]
    (h00 : (WeierstrassCurve.tateNormalForm b c).toAffine.Nonsingular 0 0) :
    addOrderOf (Affine.Point.some 0 0 h00) ≠ 17 :=
  sorry

/-- **No rational point of order `17`** (PROVEN 2026-07-25 from the
Tate-coordinate node above through `no_torsion_order_of_tateNormalForm`):
a point of order `17 ≥ 4` puts its curve in Tate normal form at the
origin, so the general statement follows from the one about the
explicit family. All the mathematical content is in the node above,
whose docstring carries this level's citation and audit. -/
theorem WeierstrassCurve.no_torsion_order_17 (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (Q : (E⁄ℚ).Point) : addOrderOf Q ≠ 17 :=
  WeierstrassCurve.no_torsion_order_of_tateNormalForm (by norm_num)
    (fun b c hell h00 =>
      @WeierstrassCurve.tateNormalForm_origin_order_ne_17 b c hell h00) E Q

/-- **No rational point of order `19`** (sorry node — IRREDUCIBLE
literature citation, audited 2026-07-25): `X_1(19)` has genus `7` and no
non-cuspidal rational point (Mazur 1977, Thm 7).

The `X_0` shortcut is NOT available: `19` is in Kenku's list. The
witness is the CM curve of discriminant `−19`, `j = −884736`, whose
cyclic isogeny degrees are exactly `{1, 19}` (PARI/GP `ellisomat`,
untrusted searcher) — the class number of the order of discriminant
`−19` is `1`, which is precisely why the `19`-isogeny is rational. 
STATED IN TATE COORDINATES (2026-07-25). The general form of this
level — no rational point of order `19` on ANY elliptic curve over
`ℚ` — is `no_torsion_order_19` just below, and is PROVEN from this
node. Here the curve is the explicit two-parameter family
`tateNormalForm b c` and the point is the origin, so this node IS the
plane model of `X_1(19)` in the `(b, c)`-coordinates rather than a
statement quantified over all curves. The passage between the two is
the PROVEN `exists_tateNormalForm`; everything above about genus,
witnesses and citation is unchanged by the restatement.
-/
theorem WeierstrassCurve.tateNormalForm_origin_order_ne_19 (b c : ℚ)
    [(WeierstrassCurve.tateNormalForm b c).IsElliptic]
    (h00 : (WeierstrassCurve.tateNormalForm b c).toAffine.Nonsingular 0 0) :
    addOrderOf (Affine.Point.some 0 0 h00) ≠ 19 :=
  sorry

/-- **No rational point of order `19`** (PROVEN 2026-07-25 from the
Tate-coordinate node above through `no_torsion_order_of_tateNormalForm`):
a point of order `19 ≥ 4` puts its curve in Tate normal form at the
origin, so the general statement follows from the one about the
explicit family. All the mathematical content is in the node above,
whose docstring carries this level's citation and audit. -/
theorem WeierstrassCurve.no_torsion_order_19 (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (Q : (E⁄ℚ).Point) : addOrderOf Q ≠ 19 :=
  WeierstrassCurve.no_torsion_order_of_tateNormalForm (by norm_num)
    (fun b c hell h00 =>
      @WeierstrassCurve.tateNormalForm_origin_order_ne_19 b c hell h00) E Q

/-- **No rational point of order `37`** (sorry node — IRREDUCIBLE
literature citation, audited 2026-07-25): `X_1(37)` has genus `40` and
no non-cuspidal rational point (Mazur 1977, Thm 7).

The `X_0` shortcut is NOT available: `37` is in Kenku's list, and
`X_0(37)` has two non-cuspidal rational points, `j = −7 · 11³` (checked
to have cyclic isogeny degrees exactly `{1, 37}` with PARI/GP
`ellisomat`, untrusted searcher) and `j = −7 · 137³ · 2083³`. At this
genus no explicit descent is available even in the literature: the
level is settled by the Eisenstein-ideal argument itself. 
STATED IN TATE COORDINATES (2026-07-25). The general form of this
level — no rational point of order `37` on ANY elliptic curve over
`ℚ` — is `no_torsion_order_37` just below, and is PROVEN from this
node. Here the curve is the explicit two-parameter family
`tateNormalForm b c` and the point is the origin, so this node IS the
plane model of `X_1(37)` in the `(b, c)`-coordinates rather than a
statement quantified over all curves. The passage between the two is
the PROVEN `exists_tateNormalForm`; everything above about genus,
witnesses and citation is unchanged by the restatement.
-/
theorem WeierstrassCurve.tateNormalForm_origin_order_ne_37 (b c : ℚ)
    [(WeierstrassCurve.tateNormalForm b c).IsElliptic]
    (h00 : (WeierstrassCurve.tateNormalForm b c).toAffine.Nonsingular 0 0) :
    addOrderOf (Affine.Point.some 0 0 h00) ≠ 37 :=
  sorry

/-- **No rational point of order `37`** (PROVEN 2026-07-25 from the
Tate-coordinate node above through `no_torsion_order_of_tateNormalForm`):
a point of order `37 ≥ 4` puts its curve in Tate normal form at the
origin, so the general statement follows from the one about the
explicit family. All the mathematical content is in the node above,
whose docstring carries this level's citation and audit. -/
theorem WeierstrassCurve.no_torsion_order_37 (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (Q : (E⁄ℚ).Point) : addOrderOf Q ≠ 37 :=
  WeierstrassCurve.no_torsion_order_of_tateNormalForm (by norm_num)
    (fun b c hell h00 =>
      @WeierstrassCurve.tateNormalForm_origin_order_ne_37 b c hell h00) E Q

/-- **No rational point of order `43`** (sorry node — IRREDUCIBLE
literature citation, audited 2026-07-25): `X_1(43)` has genus `57` and
no non-cuspidal rational point (Mazur 1977, Thm 7).

The `X_0` shortcut is NOT available: `43` is in Kenku's list, the
witness being the class-number-one CM curve of discriminant `−43`,
`j = −884736000`, whose cyclic isogeny degrees are exactly `{1, 43}`
(PARI/GP `ellisomat`, untrusted searcher). 
STATED IN TATE COORDINATES (2026-07-25). The general form of this
level — no rational point of order `43` on ANY elliptic curve over
`ℚ` — is `no_torsion_order_43` just below, and is PROVEN from this
node. Here the curve is the explicit two-parameter family
`tateNormalForm b c` and the point is the origin, so this node IS the
plane model of `X_1(43)` in the `(b, c)`-coordinates rather than a
statement quantified over all curves. The passage between the two is
the PROVEN `exists_tateNormalForm`; everything above about genus,
witnesses and citation is unchanged by the restatement.
-/
theorem WeierstrassCurve.tateNormalForm_origin_order_ne_43 (b c : ℚ)
    [(WeierstrassCurve.tateNormalForm b c).IsElliptic]
    (h00 : (WeierstrassCurve.tateNormalForm b c).toAffine.Nonsingular 0 0) :
    addOrderOf (Affine.Point.some 0 0 h00) ≠ 43 :=
  sorry

/-- **No rational point of order `43`** (PROVEN 2026-07-25 from the
Tate-coordinate node above through `no_torsion_order_of_tateNormalForm`):
a point of order `43 ≥ 4` puts its curve in Tate normal form at the
origin, so the general statement follows from the one about the
explicit family. All the mathematical content is in the node above,
whose docstring carries this level's citation and audit. -/
theorem WeierstrassCurve.no_torsion_order_43 (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (Q : (E⁄ℚ).Point) : addOrderOf Q ≠ 43 :=
  WeierstrassCurve.no_torsion_order_of_tateNormalForm (by norm_num)
    (fun b c hell h00 =>
      @WeierstrassCurve.tateNormalForm_origin_order_ne_43 b c hell h00) E Q

/-- **No rational point of order `67`** (sorry node — IRREDUCIBLE
literature citation, audited 2026-07-25): `X_1(67)` has genus `155` and
no non-cuspidal rational point (Mazur 1977, Thm 7).

The `X_0` shortcut is NOT available: `67` is in Kenku's list, the
witness being the class-number-one CM curve of discriminant `−67`,
`j = −147197952000`, whose cyclic isogeny degrees are exactly `{1, 67}`
(PARI/GP `ellisomat`, untrusted searcher). 
STATED IN TATE COORDINATES (2026-07-25). The general form of this
level — no rational point of order `67` on ANY elliptic curve over
`ℚ` — is `no_torsion_order_67` just below, and is PROVEN from this
node. Here the curve is the explicit two-parameter family
`tateNormalForm b c` and the point is the origin, so this node IS the
plane model of `X_1(67)` in the `(b, c)`-coordinates rather than a
statement quantified over all curves. The passage between the two is
the PROVEN `exists_tateNormalForm`; everything above about genus,
witnesses and citation is unchanged by the restatement.
-/
theorem WeierstrassCurve.tateNormalForm_origin_order_ne_67 (b c : ℚ)
    [(WeierstrassCurve.tateNormalForm b c).IsElliptic]
    (h00 : (WeierstrassCurve.tateNormalForm b c).toAffine.Nonsingular 0 0) :
    addOrderOf (Affine.Point.some 0 0 h00) ≠ 67 :=
  sorry

/-- **No rational point of order `67`** (PROVEN 2026-07-25 from the
Tate-coordinate node above through `no_torsion_order_of_tateNormalForm`):
a point of order `67 ≥ 4` puts its curve in Tate normal form at the
origin, so the general statement follows from the one about the
explicit family. All the mathematical content is in the node above,
whose docstring carries this level's citation and audit. -/
theorem WeierstrassCurve.no_torsion_order_67 (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (Q : (E⁄ℚ).Point) : addOrderOf Q ≠ 67 :=
  WeierstrassCurve.no_torsion_order_of_tateNormalForm (by norm_num)
    (fun b c hell h00 =>
      @WeierstrassCurve.tateNormalForm_origin_order_ne_67 b c hell h00) E Q

/-- **No rational point of order `163`** (sorry node — IRREDUCIBLE
literature citation, audited 2026-07-25): `X_1(163)` has genus `1027`
and no non-cuspidal rational point (Mazur 1977, Thm 7).

The `X_0` shortcut is NOT available: `163` is in Kenku's list, the
witness being the class-number-one CM curve of discriminant `−163`,
`j = −262537412640768000`, whose cyclic isogeny degrees are exactly
`{1, 163}` (PARI/GP `ellisomat`, untrusted searcher). This is the
largest rational isogeny degree over `ℚ`, and the level where every
explicit method is furthest out of reach. 
STATED IN TATE COORDINATES (2026-07-25). The general form of this
level — no rational point of order `163` on ANY elliptic curve over
`ℚ` — is `no_torsion_order_163` just below, and is PROVEN from this
node. Here the curve is the explicit two-parameter family
`tateNormalForm b c` and the point is the origin, so this node IS the
plane model of `X_1(163)` in the `(b, c)`-coordinates rather than a
statement quantified over all curves. The passage between the two is
the PROVEN `exists_tateNormalForm`; everything above about genus,
witnesses and citation is unchanged by the restatement.
-/
theorem WeierstrassCurve.tateNormalForm_origin_order_ne_163 (b c : ℚ)
    [(WeierstrassCurve.tateNormalForm b c).IsElliptic]
    (h00 : (WeierstrassCurve.tateNormalForm b c).toAffine.Nonsingular 0 0) :
    addOrderOf (Affine.Point.some 0 0 h00) ≠ 163 :=
  sorry

/-- **No rational point of order `163`** (PROVEN 2026-07-25 from the
Tate-coordinate node above through `no_torsion_order_of_tateNormalForm`):
a point of order `163 ≥ 4` puts its curve in Tate normal form at the
origin, so the general statement follows from the one about the
explicit family. All the mathematical content is in the node above,
whose docstring carries this level's citation and audit. -/
theorem WeierstrassCurve.no_torsion_order_163 (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (Q : (E⁄ℚ).Point) : addOrderOf Q ≠ 163 :=
  WeierstrassCurve.no_torsion_order_of_tateNormalForm (by norm_num)
    (fun b c hell h00 =>
      @WeierstrassCurve.tateNormalForm_origin_order_ne_163 b c hell h00) E Q

/-- **The eight prime levels that survive the `X_0` cut** (PROVEN
2026-07-25 — pure arithmetic over the list): a prime `ℓ ≥ 11` lying in
Kenku's list of rational cyclic isogeny degrees is one of
`11, 13, 17, 19, 37, 43, 67, 163`. The list
`{1, …, 19, 21, 25, 27, 37, 43, 67, 163}` loses `1, …, 10` to the size
hypothesis and `12, 14, 15, 16, 18, 21, 25, 27` to primality; nothing
else is deleted, and nothing else survives. -/
lemma MazurPrimeLevel.mem_of_prime_ge_eleven {ℓ : ℕ} (hℓ : ℓ.Prime) (h11 : 11 ≤ ℓ)
    (h : ℓ ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
      21, 25, 27, 37, 43, 67, 163} : Finset ℕ)) :
    ℓ ∈ ({11, 13, 17, 19, 37, 43, 67, 163} : Finset ℕ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | omega
      | exact absurd hℓ (by decide)

/-- **Mazur: no rational torsion point of prime order `≥ 11`** (PROVEN
2026-07-25 as the eight-way case split over the primes that survive the
`X_0` cut): no elliptic curve over `ℚ` has a rational point of order `ℓ`
for a prime `ℓ ≥ 11`. Mazur, "Modular curves and the Eisenstein ideal"
(Publ. Math. IHÉS 47, 1977), Thm 7.

The proof is the reduction described in the section note above and
nothing more. A point of order `ℓ` generates a rational cyclic
`ℓ`-isogeny (`mem_cyclicIsogenyDegrees_of_addOrderOf`), so `ℓ` lies in
Kenku's list; being prime and `≥ 11` it is one of the eight levels
`11, 13, 17, 19, 37, 43, 67, 163` (`MazurPrimeLevel.mem_of_prime_ge_eleven`),
each of which is a separate node above. Every prime `ℓ ≥ 11` outside
those eight — infinitely many — is discharged outright by Mazur's
isogeny theorem.

The mathematical content that remains is entirely in the eight nodes,
all IRREDUCIBLE at this mathlib pin, and in the `X_0` node
`prime_mem_cyclicIsogenyDegrees` they are cut against. The dependence on
that node is now explicit in the tree instead of being folded into the
same `sorry`: this theorem and the isogeny theorem always shared their
citation, and the section note records why using one for the other is a
reduction and not a circle. -/
theorem WeierstrassCurve.no_prime_torsion_ge_eleven (E : WeierstrassCurve ℚ)
    [E.IsElliptic] {ℓ : ℕ} (hℓ : ℓ.Prime) (h11 : 11 ≤ ℓ) (Q : (E⁄ℚ).Point) :
    addOrderOf Q ≠ ℓ := by
  intro hQ
  have h := MazurPrimeLevel.mem_of_prime_ge_eleven hℓ h11
    (E.mem_cyclicIsogenyDegrees_of_addOrderOf Q (by omega) hQ)
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [E.no_torsion_order_11 Q hQ, E.no_torsion_order_13 Q hQ,
    E.no_torsion_order_17 Q hQ, E.no_torsion_order_19 Q hQ,
    E.no_torsion_order_37 Q hQ, E.no_torsion_order_43 Q hQ,
    E.no_torsion_order_67 Q hQ, E.no_torsion_order_163 Q hQ]

/-- **No rational point of order `2` together with a rational point of
order `7`** (sorry node — the `X_1(14)` content in its level-structure
form): no elliptic curve over `ℚ` carries both. The hypotheses say
exactly that `E(ℚ) ⊇ ℤ/2 ⊕ ℤ/7 ≅ ℤ/14`, i.e. that the pair `(E, P + Q)`
is a non-cuspidal rational point of `X_1(14)` — a curve of genus `1`
(standard formula, recomputed 2026-07-25: `μ/12 = 6`, `12` cusps, so
`g = 1 + 6 − 6 = 1`) whose Jacobian has Mordell–Weil rank `0` over `ℚ`,
so `X_1(14)(ℚ)` is finite and cuspidal (Kubert; Ligozat; subsumed in
Mazur 1977, Thm 8).

IRREDUCIBLE at this mathlib pin (audit 2026-07-25). This is the sharp
form of the level: it is *equivalent* to `no_torsion_order_14` below
(`P + Q` has order `14`; conversely `7Q` and `2Q`), but it exhibits the
level structure as the fibre product `X_1(2) ×_{X_1(1)} X_1(7)`, which
is where an elementary attack would have to start. Routes checked and
rejected:

* *The `X_0` / isogeny shortcut is NOT available here* (unlike levels
  `20, 24, 35, 49`). `14` really is a rational cyclic isogeny degree:
  the curve `[a₁,a₂,a₃,a₄,a₆] = [1,−1,0,−2,−1]` of conductor `49` has
  isogeny-degree set `{1, 2, 7, 14}` (PARI/GP `ellisomat`, witness
  recomputed 2026-07-25). So `X_0(14)` has non-cuspidal rational points
  and only the `X_1(14)` statement excludes an order-`14` point.
* *Divisor reduction fails by design.* Every proper divisor of `14`
  (`1, 2, 7`) lies in Mazur's allowed set `{1, …, 10, 12}`, so no other
  node here implies this one.
* *Reduction plus Hasse only bounds the conductor.* `14 ∣ #Ẽ(𝔽_p)` at
  every odd prime `p` of good reduction and `7 ∣ #Ẽ(𝔽_2)` at `p = 2`;
  since `p + 1 + 2√p < 14` for `p ≤ 7` and `#Ẽ(𝔽_2) ≤ 5 < 7`, this
  forces bad reduction at `2, 3, 5, 7`, i.e. `210 ∣ N_E` — a lower bound
  on the conductor, never a contradiction.

A formal proof needs the level-`7` Tate normal form (the genus-`0`
parametrisation `b = d³ − d²`, `c = d² − d` of `X_1(7)`) together with
the `2`-torsion condition, which cuts out the genus-`1` curve
`X_1(14)`, and then a rank-`0` Mordell–Weil computation for it. Neither
the Tate normal form nor Mordell–Weil is available at this pin. -/
theorem WeierstrassCurve.not_order_two_and_order_seven_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (P Q : (E⁄ℚ).Point)
    (hP : addOrderOf P = 2) (hQ : addOrderOf Q = 7) : False :=
  sorry

/-- **No rational point of order `14`** (DERIVED 2026-07-25 from the
level-structure leaf `not_order_two_and_order_seven_point` by splitting
`ℤ/14` into its `2`- and `7`-primary parts): a point `Q` of order `14`
gives the order-`2` point `7 • Q` and the order-`7` point `2 • Q`.
`X_1(14)` has genus `1` and its Jacobian has Mordell–Weil rank `0` over
`ℚ`, so `X_1(14)(ℚ)` is finite and consists of cusps (Kubert–Ligozat;
subsumed in Mazur 1977, Thm 8). -/
theorem WeierstrassCurve.no_torsion_order_14 (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (Q : (E⁄ℚ).Point) : addOrderOf Q ≠ 14 := by
  intro hQ
  refine E.not_order_two_and_order_seven_point ((7 : ℕ) • Q) ((2 : ℕ) • Q) ?_ ?_
  · rw [addOrderOf_nsmul' Q (by decide), hQ]; decide
  · rw [addOrderOf_nsmul' Q (by decide), hQ]; decide

/-!
### Tate normal form at a rational point of order `5` (2026-07-25)

Machinery built to decompose `not_order_three_and_order_five_point`, whose
docstring previously read "IRREDUCIBLE at this mathlib pin"; that audit is
hereby superseded — the level-`5` genus-`0` parametrisation it named as
missing is supplied below, and the node is now DERIVED.

The classical normalisation (Tate; Kubert, *Universal bounds on the torsion
of elliptic curves*, Proc. LMS 33 (1976), §2) says that an elliptic curve
carrying a rational point `Q` of order `N ≥ 4` is `ℚ`-isomorphic, by a change
of variables carrying `Q` to `(0, 0)`, to
`E(b, c) : y² + (1 − c) x y − b y = x³ − b x²` (`WeierstrassCurve.tateNF`),
and that the exact order of `(0, 0)` is a polynomial condition on `(b, c)`.
Only `N = 5` is needed here, where the condition is `c = b`; the resulting
one-parameter family `E(b, b)` IS the genus-`0` modular curve `X_1(5)`.

Everything in this section is PROVEN. It rests on the project's
`Affine.Point.equivVariableChange` (the group isomorphism
`(C • W).Point ≃+ W.Point` induced by an admissible change of variables),
which is what makes a normal form usable on the *group of points* rather than
merely on equations — mathlib has no such transport.

The construction, for `Q = (x₀, y₀)` a point of order `5` on `W`:

* `A₃ := a₃ + x₀ a₁ + 2 y₀` is the `a₃`-coefficient after translating `Q` to
  the origin. It equals `y₀ − negY(x₀, y₀)`, so it is nonzero exactly because
  `2 • Q ≠ 0`.
* `A₄ := a₄ + 2 x₀ a₂ − y₀ a₁ + 3 x₀²`; the shear `s := A₄ / A₃` kills the
  `a₄`-coefficient.
* `A₂ := a₂ + 3 x₀ − s a₁ − s²` is the `a₂`-coefficient after those two steps.
  It is nonzero exactly because `3 • Q ≠ 0`: were it zero the curve would be
  `y² + α x y + A₃ y = x³`, on which `(0, 0)` satisfies `2P = −P` outright
  (`three_nsmul_zero_of_a₂_eq_zero`).
* the scaling by `u := A₃ / A₂` then equalises the `a₂`- and
  `a₃`-coefficients, giving `E(b, c)` with `b = −A₂³/A₃²` and
  `c = 1 − (A₂/A₃)(a₁ + 2 s)`.

On `E(b, c)` the group law gives `2 · (0,0) = (b, bc)` (`tateNF_double`) and
`3 · (0,0) = (c, b − c)` (`tateNF_triple`), while `−2 · (0,0) = (b, 0)`; so
`5 · (0,0) = 0` forces `c = b` (`tateNF_c_eq_b_of_order_five`).
-/

namespace WeierstrassCurve

/-- **The Tate normal form** `y² + (1 − c) x y − b y = x³ − b x²`, i.e. the
Weierstrass curve `⟨1 − c, −b, −b, 0, 0⟩`. Its origin `(0, 0)` is a rational
point of order `≥ 4` whenever the curve is elliptic, and every elliptic curve
over `ℚ` with a marked rational point of order `≥ 4` is `ℚ`-isomorphic to one
of these with the marked point at the origin (Kubert, Proc. LMS 33 (1976),
§2). -/
def tateNF (b c : ℚ) : WeierstrassCurve ℚ := ⟨1 - c, -b, -b, 0, 0⟩

@[simp] lemma tateNF_a₁ (b c : ℚ) : (tateNF b c).a₁ = 1 - c := rfl
@[simp] lemma tateNF_a₂ (b c : ℚ) : (tateNF b c).a₂ = -b := rfl
@[simp] lemma tateNF_a₃ (b c : ℚ) : (tateNF b c).a₃ = -b := rfl
@[simp] lemma tateNF_a₄ (b c : ℚ) : (tateNF b c).a₄ = 0 := rfl
@[simp] lemma tateNF_a₆ (b c : ℚ) : (tateNF b c).a₆ = 0 := rfl

/-- The Tate normal form degenerates at `b = 0` (there `(0,0)` would be the
singular point). -/
lemma tateNF_Δ_of_b_eq_zero (c : ℚ) : (tateNF 0 c).Δ = 0 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, tateNF_a₁, tateNF_a₂, tateNF_a₃, tateNF_a₄, tateNF_a₆]
  ring

lemma tateNF_b_ne_zero {b c : ℚ} [(tateNF b c).IsElliptic] : b ≠ 0 := by
  rintro rfl
  exact (isUnit_iff_ne_zero.mp (tateNF 0 c).isUnit_Δ) (tateNF_Δ_of_b_eq_zero c)

/-- The marked point `(0, 0)` of the Tate normal form. -/
lemma tateNF_nonsingular_zero {b c : ℚ} (hb : b ≠ 0) :
    (tateNF b c).toAffine.Nonsingular 0 0 :=
  Affine.nonsingular_zero.mpr ⟨tateNF_a₆ b c, Or.inl (by simpa using hb)⟩

/-- `−(0, 0) = (0, b)` on the Tate normal form. -/
lemma tateNF_negY_zero (b c : ℚ) : (tateNF b c).toAffine.negY 0 0 = b := by
  simp only [Affine.negY, tateNF_a₁, tateNF_a₃]; ring

lemma tateNF_equation_two (b c : ℚ) : (tateNF b c).toAffine.Equation b (b * c) := by
  rw [Affine.equation_iff]
  simp only [tateNF_a₁, tateNF_a₂, tateNF_a₃, tateNF_a₄, tateNF_a₆]; ring

lemma tateNF_equation_three (b c : ℚ) : (tateNF b c).toAffine.Equation c (b - c) := by
  rw [Affine.equation_iff]
  simp only [tateNF_a₁, tateNF_a₂, tateNF_a₃, tateNF_a₄, tateNF_a₆]; ring

/-- On the Tate normal form, `2 · (0, 0) = (b, bc)`. The tangent at `(0, 0)`
is horizontal (`slope = 0`) because `a₄ = 0`. -/
lemma tateNF_double {b c : ℚ} (hb : b ≠ 0)
    (h0 : (tateNF b c).toAffine.Nonsingular 0 0)
    (h2 : (tateNF b c).toAffine.Nonsingular b (b * c)) :
    (Point.some 0 0 h0 + Point.some 0 0 h0 : (tateNF b c).toAffine.Point) =
      Point.some b (b * c) h2 := by
  have hy : (0 : ℚ) ≠ (tateNF b c).toAffine.negY 0 0 := by
    rw [tateNF_negY_zero]; exact fun h => hb h.symm
  have hsl : (tateNF b c).toAffine.slope 0 0 0 0 = 0 := by
    rw [Affine.slope_of_Y_ne rfl hy, tateNF_negY_zero]
    simp only [tateNF_a₁, tateNF_a₂, tateNF_a₄]
    norm_num
  rw [Point.add_self_of_Y_ne hy]
  refine Point.some_eq_some _ ?_ ?_ <;>
    simp only [Affine.addX, Affine.addY, Affine.negAddY, Affine.negY, hsl, tateNF_a₁, tateNF_a₂,
      tateNF_a₃] <;> ring

/-- On the Tate normal form, `3 · (0, 0) = (c, b − c)`: the chord through
`(0, 0)` and `2 · (0, 0) = (b, bc)` has slope `c`. -/
lemma tateNF_triple {b c : ℚ} (hb : b ≠ 0)
    (h0 : (tateNF b c).toAffine.Nonsingular 0 0)
    (h2 : (tateNF b c).toAffine.Nonsingular b (b * c))
    (h3 : (tateNF b c).toAffine.Nonsingular c (b - c)) :
    (Point.some 0 0 h0 + Point.some b (b * c) h2 : (tateNF b c).toAffine.Point) =
      Point.some c (b - c) h3 := by
  have hxy : ¬((0 : ℚ) = b ∧ (0 : ℚ) = (tateNF b c).toAffine.negY b (b * c)) := by
    rintro ⟨h, -⟩; exact hb h.symm
  have hsl : (tateNF b c).toAffine.slope 0 b 0 (b * c) = c := by
    rw [Affine.slope_of_X_ne (fun h => hb h.symm)]
    field_simp
    ring
  rw [Point.add_some hxy]
  refine Point.some_eq_some _ ?_ ?_ <;>
    simp only [Affine.addX, Affine.addY, Affine.negAddY, Affine.negY, hsl, tateNF_a₁, tateNF_a₂,
      tateNF_a₃] <;> ring

/-- **Order five forces `c = b`** (PROVEN 2026-07-25): if the origin of the
Tate normal form `E(b, c)` is killed by `5`, then `c = b`. Indeed
`3 · (0,0) = (c, b − c)` and `−2 · (0,0) = (b, 0)`, and `5 · (0,0) = 0` says
exactly that these agree. This is the level-`5` half of Kubert's table, and
identifies `E(b, b)` as the universal curve over `X_1(5)`. -/
theorem tateNF_c_eq_b_of_order_five {b c : ℚ} [(tateNF b c).IsElliptic]
    (h0 : (tateNF b c).toAffine.Nonsingular 0 0)
    (h5 : (5 : ℕ) • (Point.some 0 0 h0 : (tateNF b c).toAffine.Point) = 0) : c = b := by
  have hb : b ≠ 0 := tateNF_b_ne_zero (b := b) (c := c)
  have h2 : (tateNF b c).toAffine.Nonsingular b (b * c) :=
    Affine.equation_iff_nonsingular.mp (tateNF_equation_two b c)
  have h3 : (tateNF b c).toAffine.Nonsingular c (b - c) :=
    Affine.equation_iff_nonsingular.mp (tateNF_equation_three b c)
  have e5 : (5 : ℕ) • (Point.some 0 0 h0 : (tateNF b c).toAffine.Point) =
      (Point.some 0 0 h0 + (Point.some 0 0 h0 + Point.some 0 0 h0)) +
        (Point.some 0 0 h0 + Point.some 0 0 h0) := by
    rw [show (5 : ℕ) = 4 + 1 from rfl, succ_nsmul, show (4 : ℕ) = 3 + 1 from rfl, succ_nsmul,
      show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul, two_nsmul]
    abel
  rw [e5] at h5
  have hneg : (Point.some 0 0 h0 + (Point.some 0 0 h0 + Point.some 0 0 h0) :
      (tateNF b c).toAffine.Point) = -(Point.some 0 0 h0 + Point.some 0 0 h0) := by
    rw [eq_neg_iff_add_eq_zero]; exact h5
  rw [tateNF_double hb h0 h2, tateNF_triple hb h0 h2 h3, Point.neg_some] at hneg
  injection hneg with hx hy

/-- If `a₂ = a₄ = 0` and `a₃ ≠ 0` then the origin satisfies `2P = −P`, hence
is killed by `3`. This is the degenerate case that the Tate normalisation must
avoid, and it is exactly the level-`3` normal form `y² + a₁ x y + a₃ y = x³`. -/
lemma three_nsmul_zero_of_a₂_eq_zero {V : WeierstrassCurve ℚ}
    (ha₂ : V.a₂ = 0) (ha₄ : V.a₄ = 0) (ha₃ : V.a₃ ≠ 0)
    (h0 : V.toAffine.Nonsingular 0 0) :
    (3 : ℕ) • (Point.some 0 0 h0 : V.toAffine.Point) = 0 := by
  have hnegY : V.toAffine.negY 0 0 = -V.a₃ := by simp [Affine.negY]
  have hy : (0 : ℚ) ≠ V.toAffine.negY 0 0 := by
    rw [hnegY]
    intro h
    exact ha₃ (by linarith)
  have hsl : V.toAffine.slope 0 0 0 0 = 0 := by
    rw [Affine.slope_of_Y_ne rfl hy, hnegY, ha₄]
    norm_num
  have hdbl : (Point.some 0 0 h0 + Point.some 0 0 h0 : V.toAffine.Point)
      = -Point.some 0 0 h0 := by
    rw [Point.add_self_of_Y_ne hy, Point.neg_some]
    refine Point.some_eq_some _ ?_ ?_ <;>
      simp only [Affine.addX, Affine.addY, Affine.negAddY, Affine.negY, hsl, ha₂] <;> ring
  rw [show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul, two_nsmul, hdbl, neg_add_cancel]

/-- **Tate normal form at a rational point of order `5`** (PROVEN
2026-07-25): an elliptic curve over `ℚ` carrying a rational point of order
`5` is `ℚ`-isomorphic — as a group of rational points — to the curve
`E(b, b) : y² + (1 − b) x y − b y = x³ − b x²` for some `b`. Equivalently,
`E(b, b)` is the universal elliptic curve over the genus-`0` modular curve
`X_1(5)`, with `b` its coordinate.

The isomorphism is produced explicitly (translate the point to the origin,
shear to kill `a₄`, scale to equalise `a₂` and `a₃`) and transported to the
groups of points by `Affine.Point.equivVariableChange`; the identification
`c = b` is `tateNF_c_eq_b_of_order_five`. See the section header above for the
formulas. -/
theorem exists_tateNF_equiv_of_order_five (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (Q : W.toAffine.Point) (hQ : addOrderOf Q = 5) :
    ∃ b : ℚ, ∃ _ : (tateNF b b).IsElliptic,
      Nonempty ((tateNF b b).toAffine.Point ≃+ W.toAffine.Point) := by
  have h5Q : (5 : ℕ) • Q = 0 := by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q
  have h2Q : (2 : ℕ) • Q ≠ 0 := by
    intro h
    have hd := addOrderOf_dvd_of_nsmul_eq_zero h
    rw [hQ] at hd; norm_num at hd
  have h3Q : (3 : ℕ) • Q ≠ 0 := by
    intro h
    have hd := addOrderOf_dvd_of_nsmul_eq_zero h
    rw [hQ] at hd; norm_num at hd
  have hQ0 : Q ≠ 0 := by
    intro h
    rw [h, addOrderOf_zero] at hQ
    norm_num at hQ
  obtain _ | ⟨xQ, yQ, hns⟩ := Q
  · exact absurd rfl hQ0
  have heq : yQ ^ 2 + W.a₁ * xQ * yQ + W.a₃ * yQ
      = xQ ^ 3 + W.a₂ * xQ ^ 2 + W.a₄ * xQ + W.a₆ := by
    have h := hns.1
    rwa [Affine.equation_iff] at h
  -- The coefficients after translating `Q` to the origin and shearing.
  set A₃ : ℚ := W.a₃ + xQ * W.a₁ + 2 * yQ with hA₃
  have hA₃ne : A₃ ≠ 0 := by
    intro h
    refine h2Q ?_
    rw [two_nsmul]
    refine Point.add_self_of_Y_eq ?_
    simp only [Affine.negY]
    rw [hA₃] at h
    linarith
  set A₄ : ℚ := W.a₄ + 2 * xQ * W.a₂ - yQ * W.a₁ + 3 * xQ ^ 2 with hA₄
  set s : ℚ := A₄ / A₃ with hsdef
  set A₂ : ℚ := W.a₂ + 3 * xQ - s * W.a₁ - s ^ 2 with hA₂
  -- The shear-and-translate change of variables (`u = 1`).
  have hC₀ : (⟨1, xQ, s, yQ⟩ : VariableChange ℚ) • W
      = (⟨W.a₁ + 2 * s, A₂, A₃, 0, 0⟩ : WeierstrassCurve ℚ) := by
    ext
    · rw [variableChange_a₁]; simp
    · rw [variableChange_a₂]; simp [hA₂]; ring
    · rw [variableChange_a₃]; simp [hA₃]
    · rw [variableChange_a₄]; simp only [inv_one, Units.val_one, one_pow, one_mul]
      rw [hsdef]; field_simp [hA₄, hA₃]; ring
    · rw [variableChange_a₆]; simp only [inv_one, Units.val_one, one_pow, one_mul]
      linarith [heq]
  -- `A₂ = 0` would make the origin a point of order `3`.
  have hA₂ne : A₂ ≠ 0 := by
    intro h
    refine h3Q ?_
    have hV : ((⟨1, xQ, s, yQ⟩ : VariableChange ℚ) • W).a₂ = 0 := by rw [hC₀]; exact h
    have hV4 : ((⟨1, xQ, s, yQ⟩ : VariableChange ℚ) • W).a₄ = 0 := by rw [hC₀]
    have hV3 : ((⟨1, xQ, s, yQ⟩ : VariableChange ℚ) • W).a₃ ≠ 0 := by rw [hC₀]; exact hA₃ne
    have hV6 : ((⟨1, xQ, s, yQ⟩ : VariableChange ℚ) • W).a₆ = 0 := by rw [hC₀]
    have h0V : ((⟨1, xQ, s, yQ⟩ : VariableChange ℚ) • W).toAffine.Nonsingular 0 0 :=
      Affine.nonsingular_zero.mpr ⟨hV6, Or.inl hV3⟩
    have hmap : Point.equivVariableChange W ⟨1, xQ, s, yQ⟩ (Point.some 0 0 h0V)
        = Point.some xQ yQ hns := by
      rw [Point.equivVariableChange_some]
      exact Point.some_eq_some W (by simp) (by simp)
    calc (3 : ℕ) • (Point.some xQ yQ hns : W.toAffine.Point)
        = (3 : ℕ) • (Point.equivVariableChange W ⟨1, xQ, s, yQ⟩ (Point.some 0 0 h0V)) := by
          rw [hmap]
      _ = Point.equivVariableChange W ⟨1, xQ, s, yQ⟩ ((3 : ℕ) • Point.some 0 0 h0V) :=
          (map_nsmul _ _ _).symm
      _ = 0 := by
          rw [three_nsmul_zero_of_a₂_eq_zero hV hV4 hV3 h0V]; exact map_zero _
  -- The scaling that equalises `a₂` and `a₃`.
  set v : ℚˣ := Units.mk0 (A₂ / A₃) (div_ne_zero hA₂ne hA₃ne) with hv
  set bb : ℚ := -(A₂ ^ 3 / A₃ ^ 2) with hbb
  set cc : ℚ := 1 - (A₂ / A₃) * (W.a₁ + 2 * s) with hcc
  have hvv : ((v⁻¹⁻¹ : ℚˣ) : ℚ) = A₂ / A₃ := by rw [inv_inv, hv]; simp
  have hCW : (⟨v⁻¹, xQ, s, yQ⟩ : VariableChange ℚ) • W = tateNF bb cc := by
    ext
    · rw [variableChange_a₁, tateNF_a₁]
      show ((v⁻¹⁻¹ : ℚˣ) : ℚ) * (W.a₁ + 2 * s) = 1 - cc
      rw [hvv, hcc]; ring
    · rw [variableChange_a₂, tateNF_a₂]
      show ((v⁻¹⁻¹ : ℚˣ) : ℚ) ^ 2 * (W.a₂ - s * W.a₁ + 3 * xQ - s ^ 2) = -bb
      have hX : W.a₂ - s * W.a₁ + 3 * xQ - s ^ 2 = A₂ := by rw [hA₂]; ring
      rw [hvv, hbb, hX]; field_simp
    · rw [variableChange_a₃, tateNF_a₃]
      show ((v⁻¹⁻¹ : ℚˣ) : ℚ) ^ 3 * (W.a₃ + xQ * W.a₁ + 2 * yQ) = -bb
      rw [hvv, hbb, ← hA₃]; field_simp
    · rw [variableChange_a₄, tateNF_a₄]
      show ((v⁻¹⁻¹ : ℚˣ) : ℚ) ^ 4 * (W.a₄ - s * W.a₃ + 2 * xQ * W.a₂
        - (yQ + xQ * s) * W.a₁ + 3 * xQ ^ 2 - 2 * s * yQ) = 0
      rw [hvv]
      have hY : W.a₄ - s * W.a₃ + 2 * xQ * W.a₂ - (yQ + xQ * s) * W.a₁ + 3 * xQ ^ 2
          - 2 * s * yQ = A₄ - s * A₃ := by rw [hA₄, hA₃]; ring
      rw [hY, hsdef]; field_simp; ring
    · rw [variableChange_a₆, tateNF_a₆]
      show ((v⁻¹⁻¹ : ℚˣ) : ℚ) ^ 6 * (W.a₆ + xQ * W.a₄ + xQ ^ 2 * W.a₂ + xQ ^ 3
        - yQ * W.a₃ - yQ ^ 2 - xQ * yQ * W.a₁) = 0
      rw [show W.a₆ + xQ * W.a₄ + xQ ^ 2 * W.a₂ + xQ ^ 3 - yQ * W.a₃ - yQ ^ 2
          - xQ * yQ * W.a₁ = 0 from by linarith [heq]]
      ring
  haveI hell : (tateNF bb cc).IsElliptic :=
    hCW ▸ (inferInstance : ((⟨v⁻¹, xQ, s, yQ⟩ : VariableChange ℚ) • W).IsElliptic)
  have h0 : (tateNF bb cc).toAffine.Nonsingular 0 0 :=
    tateNF_nonsingular_zero (tateNF_b_ne_zero (b := bb) (c := cc))
  have h0C : ((⟨v⁻¹, xQ, s, yQ⟩ : VariableChange ℚ) • W).toAffine.Nonsingular 0 0 := by
    rw [hCW]; exact h0
  have hmapC : Point.equivVariableChange W ⟨v⁻¹, xQ, s, yQ⟩ (Point.some 0 0 h0C)
      = Point.some xQ yQ hns := by
    rw [Point.equivVariableChange_some]
    exact Point.some_eq_some W (by simp) (by simp)
  have h5C : (5 : ℕ) • (Point.some 0 0 h0C :
      ((⟨v⁻¹, xQ, s, yQ⟩ : VariableChange ℚ) • W).toAffine.Point) = 0 := by
    apply (Point.equivVariableChange W ⟨v⁻¹, xQ, s, yQ⟩).injective
    rw [map_nsmul, hmapC, map_zero]
    exact h5Q
  -- Transport to the Tate normal form and read off `c = b`.
  have h5T : (5 : ℕ) • (Point.some 0 0 h0 : (tateNF bb cc).toAffine.Point) = 0 := by
    apply (Point.equivOfEq hCW.symm).injective
    rw [map_nsmul, map_zero, Point.equivOfEq_some]
    exact h5C
  have hcb : cc = bb := tateNF_c_eq_b_of_order_five h0 h5T
  have htate : tateNF bb cc = tateNF bb bb := by rw [hcb]
  exact ⟨bb, htate ▸ hell,
    ⟨(Point.equivOfEq htate.symm).trans
      ((Point.equivOfEq hCW.symm).trans (Point.equivVariableChange W ⟨v⁻¹, xQ, s, yQ⟩))⟩⟩

/-- **`X_1(15)` has no non-cuspidal rational point** (sorry node, cut
2026-07-25 out of `not_order_three_and_order_five_point`): the Tate normal
form `E(b, b) : y² + (1 − b) x y − b y = x³ − b x²` — the universal curve over
`X_1(5)`, whose origin is a rational point of order `5` for every `b` making
it elliptic — never carries a rational point of order `3`.

This is the `X_1(15)` content in its sharpest form. `b` is the coordinate on
the genus-`0` modular curve `X_1(5)`, and the `3`-torsion condition on
`E(b, b)` cuts out of it the genus-`1` curve `X_1(15)` (recomputed
2026-07-25: `μ/12 = 8`, `16` cusps, so `g = 1 + 8 − 8 = 1`), whose Jacobian
has Mordell–Weil rank `0` over `ℚ`, so `X_1(15)(ℚ)` is finite and cuspidal
(Kubert; Ligozat; subsumed in Mazur 1977, Thm 8).

NOT VACUOUS, and both hypotheses are load-bearing: `E(b, b)` is elliptic for
every `b` outside the vanishing locus of `Δ`, the origin genuinely has order
`5` there (`tateNF_c_eq_b_of_order_five` is an equivalence in this direction:
`c = b` makes `3 · (0,0) = −2 · (0,0)`), and an order-`3` point would produce
a rational point of order `15`.

What remains, in dependency order; none of it exists at this mathlib pin:

1. *The explicit affine model of `X_1(15)`.* Translating a candidate
   `3`-torsion point `(x, y)` of `E(b, b)` to the origin must make the
   translated `a₄` vanish and the translated `b₈` vanish, i.e. — writing
   `A₂' = 3x − b`, `A₃' = (1 − b) x + 2 y − b`, `A₄' = 3x² − 2 b x − (1 − b) y`
   for the translated coefficients — the pair of equations
   `y² + (1 − b) x y − b y = x³ − b x²` and
   `A₄'² + (1 − b) A₃' A₄' = A₂' A₃'²` in `(b, x, y)`, together with
   `A₃' ≠ 0`. (The criterion "`(0,0)` has order `3` iff `a₆ = 0`, `b₈ = 0`,
   `a₃ ≠ 0`" is elementary: `2 · (0,0) = −(0,0)` reduces to
   `a₄² + a₁ a₃ a₄ − a₂ a₃² = 0`, which is `−b₈` when `a₆ = 0`.)
2. *Its reduction to a Weierstrass model* — `X_1(15)` is a curve of
   conductor `50` in the standard tables.
3. *A rank-`0` Mordell–Weil computation for that curve*, i.e. a `2`-descent
   exhibiting the Selmer group as exhausted by torsion. Mathlib has no
   descent machinery of any kind, so this is the genuinely missing theory.

Routes checked and rejected (audit 2026-07-25, carried over from the
level-structure form of this node):

* *The `X_0` / isogeny shortcut is NOT available here* (unlike levels
  `20, 24, 35, 49`). `15` is a rational cyclic isogeny degree:
  `[1,0,1,−1,−2]` of conductor `50` has isogeny-degree set `{1, 3, 5, 15}`
  (PARI/GP `ellisomat`), so `X_0(15)` has non-cuspidal rational points and
  only the `X_1` statement excludes an order-`15` point.
* *Divisor reduction fails by design.* The proper divisors `1, 3, 5` of `15`
  all lie in Mazur's allowed set `{1, …, 10, 12}`.
* *Reduction plus Hasse only bounds the conductor.* `15 ∣ #Ẽ(𝔽_p)` at every
  good `p` (including `p = 2`, since `15` is odd), and `p + 1 + 2√p < 15` for
  `p ≤ 7`, so bad reduction is forced exactly at `2, 3, 5, 7`: `210 ∣ N_E`,
  and nothing more. -/
theorem tateNF_self_no_order_three (b : ℚ) [(tateNF b b).IsElliptic]
    (P : (tateNF b b).toAffine.Point) (hP : addOrderOf P = 3) : False :=
  sorry

end WeierstrassCurve

/-- **No rational point of order `3` together with a rational point of
order `5`** (DERIVED 2026-07-25 from the Tate-normal-form reduction
`WeierstrassCurve.exists_tateNF_equiv_of_order_five` and the `X_1(15)` leaf
`WeierstrassCurve.tateNF_self_no_order_three`): no elliptic curve over `ℚ`
carries both. The hypotheses say exactly that `E(ℚ) ⊇ ℤ/3 ⊕ ℤ/5 ≅ ℤ/15`, i.e.
that `(E, P + Q)` is a non-cuspidal rational point of `X_1(15)` — a curve of
genus `1` whose Jacobian has Mordell–Weil rank `0` over `ℚ`, so `X_1(15)(ℚ)`
is finite and cuspidal (Kubert; Ligozat; subsumed in Mazur 1977, Thm 8).

The derivation normalises away the level-`5` structure: the point `Q` of order
`5` puts `E` into the Tate normal form `E(b, b)` by an explicit `ℚ`-isomorphism
of point groups, along which the order-`3` point `P` transports; what is left
is the genus-`1` statement, which is the remaining leaf. The old docstring's
claim that this node is "IRREDUCIBLE at this mathlib pin" is superseded: the
genus-`0` parametrisation of `X_1(5)` that it named as missing is now
proven. -/
theorem WeierstrassCurve.not_order_three_and_order_five_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (P Q : (E⁄ℚ).Point)
    (hP : addOrderOf P = 3) (hQ : addOrderOf Q = 5) : False := by
  obtain ⟨b, hell, ⟨Φ⟩⟩ := WeierstrassCurve.exists_tateNF_equiv_of_order_five (E⁄ℚ) Q hQ
  haveI := hell
  exact WeierstrassCurve.tateNF_self_no_order_three b (Φ.symm P)
    (by rw [← hP]; exact Φ.symm.addOrderOf_eq P)

/-- **No rational point of order `15`** (DERIVED 2026-07-25 from the
level-structure leaf `not_order_three_and_order_five_point` by
splitting `ℤ/15` into its `3`- and `5`-primary parts): a point `Q` of
order `15` gives the order-`3` point `5 • Q` and the order-`5` point
`3 • Q`. `X_1(15)` has genus `1` and its Jacobian has Mordell–Weil rank
`0` over `ℚ`, so `X_1(15)(ℚ)` is finite and consists of cusps
(Kubert–Ligozat; subsumed in Mazur 1977, Thm 8). -/
theorem WeierstrassCurve.no_torsion_order_15 (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (Q : (E⁄ℚ).Point) : addOrderOf Q ≠ 15 := by
  intro hQ
  refine E.not_order_three_and_order_five_point ((5 : ℕ) • Q) ((3 : ℕ) • Q) ?_ ?_
  · rw [addOrderOf_nsmul' Q (by decide), hQ]; decide
  · rw [addOrderOf_nsmul' Q (by decide), hQ]; decide

/-!
### The level-`16` descent: `X_1(16)` in elementary form (2026-07-25)

The docstring of `not_halved_order_eight_point` below recorded the node as
IRREDUCIBLE, needing "the genus-`2` curve `X_1(16)` and a determination of
its rational points (Ogg's descent, or Chabauty on its Jacobian)". That
audit is now SUPERSEDED: the whole chain is elementary, and everything
between the elliptic curve and a single classical Diophantine statement is
PROVEN below.

**The route.** Let `R` have order `16`, and set `P = 2R`, `Q = 4R`,
`T = 8R`. Translate the rational `2`-torsion abscissa `θ = x(T)` to the
origin and complete the square, putting the curve in the form
`Y² = X³ + aX² + bX` with `T = (0,0)`. In that form the duplication
formula collapses to a single square:

  `X(2S) = ((X(S)² − b) / (2Y(S)))²`   (`doubling_short`)

Running it along `R → P → Q → T` forces, in order:
`b = X_Q²`; `X_Q = g²` (it is a double); `X_P = f²` (likewise); so
`b = g⁴`. Scaling `(X, Y) ↦ (X/g², Y/g³)` normalises the curve to
`η² = ξ³ + (s² − 2)ξ² + ξ` with `Q = (1, s)`, `ξ_P = n²`, `n = f/g`.
The relation `2P = Q` then reads `4s²n⁴ = (n² − 1)⁴` (`param_sq`) — this
is the genus-`0` level-`8` structure — and feeding it into `2R = P`
yields, after the palindromic substitution `z = ξ + 1/ξ`, the identity

  `(n(ξ²+1) − 2n³ξ)² = (ξ(n⁴−1))²`   (`param_dichotomy`)

whose two sign branches are exchanged by `n ↦ −n`. Either way
`(n²−1)(n²+1)(n²+2n−1)` is a rational square (`sextic_of_param`). That
sextic is an affine model of `X_1(16)`; the excluded values `n ∈ {0, ±1}`
are exactly its cusps (`n² = 1` ⟺ `x(P) = x(Q)`, impossible for orders
`8` and `4`).

Sanity-checked numerically before formalising (PARI/GP): `u = 2` gives
`s = 1/4`, the curve `y² = x³ − (31/16)x² + x` with `P = (2, 3/2)` of
order exactly `8`, `Q = 2P = (1, 1/4)` of order `4`, `T = 4P = (0,0)`;
and the factorisation `(2n³+n⁴−1)² − 4n² = (n−1)(n+1)³(n²+1)(n²+2n−1)`
underlying `sextic_of_param` was confirmed symbolically.

**Nothing is left: this cluster is sorry-free (2026-07-25).** Both leaves
were closed by separate owners on the same day.

* `exists_chain_coords` — pure `Affine.Point` plumbing, zero arithmetic
  content, PROVEN from `exists_doubling_coords` and `Point.X_eq_iff`. The
  trick is that `exists_doubling_coords` takes the DOUBLED point's abscissa
  as an input rather than producing it, so the chain is walked downwards
  `T = 4P → Q = 2P → P → R` and no two coordinate namings ever need
  reconciling. `addOrderOf R = 16` turns out to be unused — only
  `R + R = P ≠ 0` — with everything else following from `addOrderOf P = 8`.
* `not_sextic_square` — PROVEN by the classical two-case descent recorded
  in its docstring. Its one genuine mathlib gap, Fermat's *other* quartic
  theorem `x⁴ − y⁴ = z² → xyz = 0`, is
  `QuarticDescent.sq_ne_quartic_sub_quartic` in the publicly imported
  `Fermat/FLT/FreyCurve/QuarticDescent.lean`, since mathlib carries only
  `not_fermat_42`.
  In the odd branch the three pairwise-coprime factors give `m² − k² = ±e²`
  and `m² + k² = c²`, and the Pythagorean identity turns that directly into
  `c⁴ − e⁴ = (2mk)²` — so the intermediate `a⁴ + b⁴ = 2c² → a² = b²` the
  original sketch went through is not needed, it reduces to the same
  quartic theorem anyway.

So `not_halved_order_eight_point` — whose recorded audit claimed it needed
the genus-2 curve `X_1(16)` and Chabauty — is now fully proven by
elementary means.
-/

namespace MazurSixteen

/-- **Duplication in short form** (PROVEN — pure field algebra): on
`Y² = X³ + aX² + bX` the doubled abscissa is the square
`((X² − b)/(2Y))²`. This is the collapse that drives the whole level-`16`
descent: it makes every doubled abscissa visibly a square, which is what
turns the `16`-torsion chain into a sequence of square conditions. -/
lemma doubling_short {a b X Y L X' : ℚ}
    (heq : Y ^ 2 = X ^ 3 + a * X ^ 2 + b * X)
    (hL : L * (2 * Y) = 3 * X ^ 2 + 2 * a * X + b)
    (hX' : L ^ 2 - a - X - X = X') :
    X' * (2 * Y) ^ 2 = (X ^ 2 - b) ^ 2 := by
  linear_combination (L * (2 * Y) + (3 * X ^ 2 + 2 * a * X + b)) * hL
    - 4 * (a + X + X) * heq - (2 * Y) ^ 2 * hX'

/-- **Reduction to short form** (PROVEN — pure field algebra): completing
the square and translating a `2`-torsion abscissa `θ` to the origin turns
the general Weierstrass equation into `Y² = X³ + aX² + bX`. The constant
term vanishes precisely because `θ` is a root of the `2`-division cubic. -/
lemma shift_equation {a₁ a₂ a₃ a₄ a₆ θ x y : ℚ}
    (heq : y ^ 2 + a₁ * x * y + a₃ * y = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
    (hθ : 4 * θ ^ 3 + (a₁ ^ 2 + 4 * a₂) * θ ^ 2 + (2 * a₁ * a₃ + 4 * a₄) * θ
        + (a₃ ^ 2 + 4 * a₆) = 0) :
    (y + (a₁ * x + a₃) / 2) ^ 2 =
      (x - θ) ^ 3 + (3 * θ + (a₁ ^ 2 + 4 * a₂) / 4) * (x - θ) ^ 2
        + (3 * θ ^ 2 + (a₁ ^ 2 + 4 * a₂) / 2 * θ + (2 * a₄ + a₁ * a₃) / 2) * (x - θ) := by
  linear_combination heq + (1 / 4 : ℚ) * hθ

/-- **The tangent slope in short form** (PROVEN — pure field algebra). -/
lemma shift_slope {a₁ a₂ a₃ a₄ θ x y l : ℚ}
    (hl : l * (2 * y + a₁ * x + a₃) = 3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y) :
    (l + a₁ / 2) * (2 * (y + (a₁ * x + a₃) / 2)) =
      3 * (x - θ) ^ 2 + 2 * (3 * θ + (a₁ ^ 2 + 4 * a₂) / 4) * (x - θ)
        + (3 * θ ^ 2 + (a₁ ^ 2 + 4 * a₂) / 2 * θ + (2 * a₄ + a₁ * a₃) / 2) := by
  linear_combination hl

/-- **The doubled abscissa in short form** (PROVEN — `ring`). -/
lemma shift_addX {a₁ a₂ θ x l : ℚ} :
    (l + a₁ / 2) ^ 2 - (3 * θ + (a₁ ^ 2 + 4 * a₂) / 4) - (x - θ) - (x - θ) =
      (l ^ 2 + a₁ * l - a₂ - x - x) - θ := by
  ring

/-- **The level-`8` relation** (PROVEN — pure field algebra): on the
normalised curve `η² = ξ³ + (s²−2)ξ² + ξ`, where `Q = (1, s)` has order `4`
and `ξ_P = n²`, the relation `2P = Q` reads `4s²n⁴ = (n²−1)⁴`. This is the
genus-`0` structure of `X_1(8)` in the coordinates of this descent. -/
lemma param_sq {n s ηP : ℚ}
    (hcurveP : ηP ^ 2 = (n ^ 2) ^ 3 + (s ^ 2 - 2) * (n ^ 2) ^ 2 + n ^ 2)
    (hdoubleP : ((n ^ 2) ^ 2 - 1) ^ 2 = 4 * ηP ^ 2) :
    4 * s ^ 2 * n ^ 4 = (n ^ 2 - 1) ^ 4 := by
  linear_combination -hdoubleP - 4 * hcurveP

/-- **The sign dichotomy** (PROVEN — pure field algebra): feeding the
level-`8` relation into `2R = P` pins `ξ = ξ_R` by
`(n(ξ²+1) − 2n³ξ)² = (ξ(n⁴−1))²`. The two branches are exchanged by
`n ↦ −n`, which is why the conclusion below may be taken with either
sign of `n`. -/
lemma param_dichotomy {n s ξ ηR : ℚ}
    (hs : 4 * s ^ 2 * n ^ 4 = (n ^ 2 - 1) ^ 4)
    (hcurve : ηR ^ 2 = ξ ^ 3 + (s ^ 2 - 2) * ξ ^ 2 + ξ)
    (hdouble : (ξ ^ 2 - 1) ^ 2 = 4 * n ^ 2 * ηR ^ 2) :
    (n * (ξ ^ 2 + 1) - 2 * n ^ 3 * ξ) ^ 2 = (ξ * (n ^ 4 - 1)) ^ 2 := by
  linear_combination n ^ 2 * hdouble + 4 * n ^ 4 * hcurve + ξ ^ 2 * hs

/-- **The point on the sextic** (PROVEN — pure field algebra): the `+`
branch of the dichotomy exhibits `(n²−1)(n²+1)(n²+2n−1)` as a square. The
underlying factorisation is
`(2n³+n⁴−1)² − 4n² = (n−1)(n+1)³(n²+1)(n²+2n−1)`. -/
lemma sextic_of_param {n ξ : ℚ} (hn1 : n + 1 ≠ 0) (hξ : ξ ≠ 0)
    (h : n * (ξ ^ 2 + 1) = ξ * (2 * n ^ 3 + n ^ 4 - 1)) :
    (n * (ξ ^ 2 - 1) / (ξ * (n + 1))) ^ 2 =
      (n ^ 2 - 1) * (n ^ 2 + 1) * (n ^ 2 + 2 * n - 1) := by
  field_simp
  linear_combination (n * (ξ ^ 2 + 1) + ξ * (2 * n ^ 3 + n ^ 4 - 1)) * h

/-- **The level-`16` chain in short form** (PROVEN): from a doubling chain
`R → P → Q → T = (0,0)` on `Y² = X³ + aX² + bX`, a rational point on the
sextic model of `X_1(16)`. The nondegeneracy hypotheses are exactly what
the orders `16, 8, 4, 2` supply: `Y_R, Y_P ≠ 0` say `R, P` are not
`2`-torsion, `X_R, X_P, X_Q ≠ 0` say none of them is `T`, and
`X_P ≠ X_Q` says `P ≠ ±Q`. -/
lemma sextic_of_short_chain {a b XR YR XP YP XQ YQ : ℚ}
    (hcR : YR ^ 2 = XR ^ 3 + a * XR ^ 2 + b * XR)
    (hcP : YP ^ 2 = XP ^ 3 + a * XP ^ 2 + b * XP)
    (hcQ : YQ ^ 2 = XQ ^ 3 + a * XQ ^ 2 + b * XQ)
    (dR : XP * (2 * YR) ^ 2 = (XR ^ 2 - b) ^ 2)
    (dP : XQ * (2 * YP) ^ 2 = (XP ^ 2 - b) ^ 2)
    (dQ : XQ ^ 2 = b)
    (hYR : YR ≠ 0) (hYP : YP ≠ 0)
    (hXR : XR ≠ 0) (hXP : XP ≠ 0) (hXQ : XQ ≠ 0) (hPQ : XP ≠ XQ) :
    ∃ n Y : ℚ, n ≠ 0 ∧ n ≠ 1 ∧ n ≠ -1 ∧
      Y ^ 2 = (n ^ 2 - 1) * (n ^ 2 + 1) * (n ^ 2 + 2 * n - 1) := by
  -- `X_Q` and `X_P` are squares, by the duplication formula
  obtain ⟨g, rfl⟩ : ∃ g, XQ = g ^ 2 :=
    ⟨(XP ^ 2 - b) / (2 * YP), by field_simp; linear_combination dP⟩
  obtain ⟨f, rfl⟩ : ∃ f, XP = f ^ 2 :=
    ⟨(XR ^ 2 - b) / (2 * YR), by field_simp; linear_combination dR⟩
  have hg0 : g ≠ 0 := by intro h; exact hXQ (by rw [h]; ring)
  have hf0 : f ≠ 0 := by intro h; exact hXP (by rw [h]; ring)
  -- hence `b = g⁴`
  subst dQ
  -- normalise: scale every coordinate by the appropriate power of `g`
  obtain ⟨s, rfl⟩ : ∃ s, YQ = s * g ^ 3 := ⟨YQ / g ^ 3, by field_simp⟩
  obtain ⟨n, rfl⟩ : ∃ n, f = n * g := ⟨f / g, by field_simp⟩
  obtain ⟨ξ, rfl⟩ : ∃ ξ, XR = ξ * g ^ 2 := ⟨XR / g ^ 2, by field_simp⟩
  obtain ⟨ηR, rfl⟩ : ∃ ηR, YR = ηR * g ^ 3 := ⟨YR / g ^ 3, by field_simp⟩
  obtain ⟨ηP, rfl⟩ : ∃ ηP, YP = ηP * g ^ 3 := ⟨YP / g ^ 3, by field_simp⟩
  -- the short-form coefficient `a` is `(s²−2)g²`
  have ha : a = (s ^ 2 - 2) * g ^ 2 := by
    have h4 : (g : ℚ) ^ 4 ≠ 0 := pow_ne_zero _ hg0
    apply mul_left_cancel₀ h4
    linear_combination -hcQ
  subst ha
  have hg6 : (g : ℚ) ^ 6 ≠ 0 := pow_ne_zero _ hg0
  have hg8 : (g : ℚ) ^ 8 ≠ 0 := pow_ne_zero _ hg0
  -- the four normalised relations
  have hcP' : ηP ^ 2 = (n ^ 2) ^ 3 + (s ^ 2 - 2) * (n ^ 2) ^ 2 + n ^ 2 := by
    apply mul_left_cancel₀ hg6; linear_combination hcP
  have hdP' : ((n ^ 2) ^ 2 - 1) ^ 2 = 4 * ηP ^ 2 := by
    apply mul_left_cancel₀ hg8; linear_combination -dP
  have hcR' : ηR ^ 2 = ξ ^ 3 + (s ^ 2 - 2) * ξ ^ 2 + ξ := by
    apply mul_left_cancel₀ hg6; linear_combination hcR
  have hdR' : (ξ ^ 2 - 1) ^ 2 = 4 * n ^ 2 * ηR ^ 2 := by
    apply mul_left_cancel₀ hg8; linear_combination -dR
  -- the level-`8` relation and the sign dichotomy
  have hs := param_sq hcP' hdP'
  have hdich := param_dichotomy hs hcR' hdR'
  -- nondegeneracy, transported to the normalised coordinates
  have hn0 : n ≠ 0 := by intro h; exact hf0 (by rw [h]; ring)
  have hξ0 : ξ ≠ 0 := by intro h; exact hXR (by rw [h]; ring)
  have hnsq : n ^ 2 ≠ 1 := by
    intro h
    exact hPQ (by rw [mul_pow, h, one_mul])
  have hn1 : n ≠ 1 := fun h => hnsq (by rw [h]; ring)
  have hnm1 : n ≠ -1 := fun h => hnsq (by rw [h]; ring)
  have hfac : (n * (ξ ^ 2 + 1) - 2 * n ^ 3 * ξ - ξ * (n ^ 4 - 1)) *
      (n * (ξ ^ 2 + 1) - 2 * n ^ 3 * ξ + ξ * (n ^ 4 - 1)) = 0 := by
    linear_combination hdich
  rcases mul_eq_zero.mp hfac with h | h
  · exact ⟨n, _, hn0, hn1, hnm1,
      sextic_of_param (by intro hc; exact hnm1 (by linarith)) hξ0 (by linear_combination h)⟩
  · exact ⟨-n, _, neg_ne_zero.mpr hn0, fun hc => hnm1 (by linarith),
      fun hc => hn1 (by linarith),
      sextic_of_param (by intro hc; exact hn1 (by linarith)) hξ0 (by linear_combination -h)⟩

/-- **Coordinates of a nonzero affine point** (PROVEN — one `rcases`). -/
lemma exists_pointCoords {W : WeierstrassCurve.Affine ℚ} (A : W.Point) (hA : A ≠ 0) :
    ∃ x y, ∃ h : W.Nonsingular x y, A = Point.some x y h := by
  rcases A with _ | ⟨x, y, h⟩
  · exact absurd rfl hA
  · exact ⟨x, y, h, rfl⟩

/-- **Coordinate data of a single doubling step** (PROVEN — pure
`Affine.Point` plumbing). If `A + A = B` with `B ≠ 0` and `B` has
coordinates `(x', y')`, then `A` is affine with coordinates `(x, y)`, its
tangent is defined (`2y + a₁x + a₃ ≠ 0`, i.e. `A` is not `2`-torsion), the
tangent slope `l` satisfies the cleared slope equation, and the duplication
formula lands on `x'`. This is the level-`16` analogue of
`MazurFourTorsion.exists_halving_coords`, threaded so that the ABSCISSA of
the doubled point is an input rather than an output — which is what lets the
whole chain `R → P → Q → T` be extracted with consistent coordinates. -/
lemma exists_doubling_coords {W : WeierstrassCurve.Affine ℚ} (A B : W.Point)
    (hAB : A + A = B) (hB0 : B ≠ 0) {x' y' : ℚ} {hns' : W.Nonsingular x' y'}
    (hBeq : B = Point.some x' y' hns') :
    ∃ x y l, ∃ hns : W.Nonsingular x y,
      A = Point.some x y hns ∧
      2 * y + W.a₁ * x + W.a₃ ≠ 0 ∧
      l * (2 * y + W.a₁ * x + W.a₃) = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y ∧
      l ^ 2 + W.a₁ * l - W.a₂ - x - x = x' := by
  rcases A with _ | ⟨x, y, hns⟩
  · exact absurd (hAB.symm.trans (add_zero 0)) hB0
  · -- `A` is not `2`-torsion: its double `B` is nonzero
    have hy : y ≠ W.negY x y := fun h =>
      hB0 (hAB.symm.trans (Point.add_self_of_Y_eq h))
    have hsub : y - W.negY x y = 2 * y + W.a₁ * x + W.a₃ := by rw [negY]; ring
    have hw : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
      rw [← hsub]; exact sub_ne_zero.mpr hy
    have hadd := Point.add_self_of_Y_ne (h₁ := hns) hy
    have hx' : W.addX x x (W.slope x x y y) = x' :=
      (Point.some.inj (hadd.symm.trans (hAB.trans hBeq))).1
    have hlm : W.slope x x y y * (2 * y + W.a₁ * x + W.a₃) =
        3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
      rw [← hsub, slope_of_Y_ne rfl hy, div_mul_cancel₀ _ (sub_ne_zero.mpr hy)]
    simp only [addX] at hx'
    exact ⟨x, y, W.slope x x y y, hns, rfl, hw, hlm, hx'⟩

/-- **Coordinate data of the level-`16` doubling chain** (PROVEN
2026-07-25 — pure mathlib `Affine.Point` plumbing, with NO arithmetic
content).

Given `P` of order `8` and `R` with `2R = P` (so `R` has order `16`), set
`Q = 2P` and `T = 2Q`, of orders `4` and `2`. The statement records what the
`Affine.Point` API already knows about that chain, in coordinates: each of
`R, P, Q` is an affine point; `θ = x(T)` is a root of the `2`-division
cubic (because `T` is `2`-torsion); each doubling is witnessed by its
tangent slope; `R` and `P` are not `2`-torsion; and none of
`x(R), x(P), x(Q)` equals `θ`, with `x(P) ≠ x(Q)`.

Every one of those follows from the orders alone. The chain is walked
DOWNWARDS with `exists_doubling_coords` — `T`'s coordinates first (it is
nonzero), then `Q`, `P`, `R` — so that the abscissa produced by each
duplication formula is literally the abscissa of the next point, with no
reconciliation step. The order bookkeeping is entirely
`addOrderOf_dvd_iff_nsmul_eq_zero`: for `0 < n < 8` one has `n • P ≠ 0`,
which gives `P ≠ 0`, `Q ≠ 0`, `T ≠ 0`, `3P ≠ 0`, while `8 • P = 0` gives
`T + T = 0`. The separations are then read off through
`WeierstrassCurve.Affine.Point.X_eq_iff` (equal abscissae ⟹ the points are
equal or negatives), using `-T = T` for the three comparisons against `θ`;
`R = T` would force `P = 2R = 2T = 0`, `P = T` and `P = -Q` would force
`3P = 0`, and `P = Q` or `Q = T` would force `P = 0` resp. `Q = 0`.
Note `addOrderOf R = 16` is never needed: only `R + R = P ≠ 0`. -/
theorem exists_chain_coords (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P R : (E⁄ℚ).Point) (hP : addOrderOf P = 8) (hR : (2 : ℕ) • R = P) :
    ∃ θ xR yR lR xP yP lP xQ yQ lQ : ℚ,
      4 * θ ^ 3 + ((E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂) * θ ^ 2
          + (2 * (E⁄ℚ).a₁ * (E⁄ℚ).a₃ + 4 * (E⁄ℚ).a₄) * θ
          + ((E⁄ℚ).a₃ ^ 2 + 4 * (E⁄ℚ).a₆) = 0 ∧
      yR ^ 2 + (E⁄ℚ).a₁ * xR * yR + (E⁄ℚ).a₃ * yR
          = xR ^ 3 + (E⁄ℚ).a₂ * xR ^ 2 + (E⁄ℚ).a₄ * xR + (E⁄ℚ).a₆ ∧
      yP ^ 2 + (E⁄ℚ).a₁ * xP * yP + (E⁄ℚ).a₃ * yP
          = xP ^ 3 + (E⁄ℚ).a₂ * xP ^ 2 + (E⁄ℚ).a₄ * xP + (E⁄ℚ).a₆ ∧
      yQ ^ 2 + (E⁄ℚ).a₁ * xQ * yQ + (E⁄ℚ).a₃ * yQ
          = xQ ^ 3 + (E⁄ℚ).a₂ * xQ ^ 2 + (E⁄ℚ).a₄ * xQ + (E⁄ℚ).a₆ ∧
      lR * (2 * yR + (E⁄ℚ).a₁ * xR + (E⁄ℚ).a₃)
          = 3 * xR ^ 2 + 2 * (E⁄ℚ).a₂ * xR + (E⁄ℚ).a₄ - (E⁄ℚ).a₁ * yR ∧
      lP * (2 * yP + (E⁄ℚ).a₁ * xP + (E⁄ℚ).a₃)
          = 3 * xP ^ 2 + 2 * (E⁄ℚ).a₂ * xP + (E⁄ℚ).a₄ - (E⁄ℚ).a₁ * yP ∧
      lQ * (2 * yQ + (E⁄ℚ).a₁ * xQ + (E⁄ℚ).a₃)
          = 3 * xQ ^ 2 + 2 * (E⁄ℚ).a₂ * xQ + (E⁄ℚ).a₄ - (E⁄ℚ).a₁ * yQ ∧
      lR ^ 2 + (E⁄ℚ).a₁ * lR - (E⁄ℚ).a₂ - xR - xR = xP ∧
      lP ^ 2 + (E⁄ℚ).a₁ * lP - (E⁄ℚ).a₂ - xP - xP = xQ ∧
      lQ ^ 2 + (E⁄ℚ).a₁ * lQ - (E⁄ℚ).a₂ - xQ - xQ = θ ∧
      2 * yR + (E⁄ℚ).a₁ * xR + (E⁄ℚ).a₃ ≠ 0 ∧
      2 * yP + (E⁄ℚ).a₁ * xP + (E⁄ℚ).a₃ ≠ 0 ∧
      xR ≠ θ ∧ xP ≠ θ ∧ xQ ≠ θ ∧ xP ≠ xQ := by
  have hRR : R + R = P := by rw [← hR, two_nsmul]
  -- order bookkeeping: `n • P ≠ 0` for `0 < n < 8`, and `8 • P = 0`
  have hord : ∀ n : ℕ, 0 < n → n < 8 → n • P ≠ 0 := by
    intro n hn0 hn8 h
    have hd : addOrderOf P ∣ n := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h
    rw [hP] at hd
    exact absurd (Nat.le_of_dvd hn0 hd) (by omega)
  have hP0 : P ≠ 0 := by
    have h := hord 1 (by norm_num) (by norm_num)
    rwa [one_nsmul] at h
  have hQ0 : P + P ≠ 0 := by
    have h := hord 2 (by norm_num) (by norm_num)
    rwa [two_nsmul] at h
  have h3P : P + P + P ≠ 0 := by
    have h := hord 3 (by norm_num) (by norm_num)
    rwa [show (3 : ℕ) • P = P + P + P by abel] at h
  have hT0 : (P + P) + (P + P) ≠ 0 := by
    have h := hord 4 (by norm_num) (by norm_num)
    rwa [show (4 : ℕ) • P = (P + P) + (P + P) by abel] at h
  have hT2 : ((P + P) + (P + P)) + ((P + P) + (P + P)) = 0 := by
    rw [show ((P + P) + (P + P)) + ((P + P) + (P + P)) = (8 : ℕ) • P by abel, ← hP]
    exact addOrderOf_nsmul_eq_zero P
  -- separations along the chain, at the level of points
  have hPQ1 : P ≠ P + P := by
    intro h
    exact hP0 (add_left_cancel (show P + 0 = P + P by rw [add_zero]; exact h)).symm
  have hPQ2 : P ≠ -(P + P) := by
    intro h
    have h2 := eq_neg_iff_add_eq_zero.mp h
    rw [← add_assoc] at h2
    exact h3P h2
  have hQT : P + P ≠ (P + P) + (P + P) := by
    intro h
    exact hQ0 (add_left_cancel
      (show (P + P) + 0 = (P + P) + (P + P) by rw [add_zero]; exact h)).symm
  have hPT : P ≠ (P + P) + (P + P) := by
    intro h
    have key : P + 0 = P + (P + P + P) := by
      rw [add_zero, show P + (P + P + P) = (P + P) + (P + P) by abel]
      exact h
    exact h3P (add_left_cancel key).symm
  have hRT : R ≠ (P + P) + (P + P) := by
    intro h
    exact hP0 (by rw [← hRR, h]; exact hT2)
  -- coordinates of `T = 4P`, then of `Q = 2P`, of `P`, of `R`
  obtain ⟨θ, u, hnsT, hTeq⟩ := exists_pointCoords _ hT0
  obtain ⟨xQ, yQ, lQ, hnsQ, hQeq, _wQ, slQ, dxQ⟩ :=
    exists_doubling_coords (P + P) ((P + P) + (P + P)) rfl hT0 hTeq
  obtain ⟨xP, yP, lP, hnsP, hPeq, wP, slP, dxP⟩ :=
    exists_doubling_coords P (P + P) rfl hQ0 hQeq
  obtain ⟨xR, yR, lR, hnsR, hReq, wR, slR, dxR⟩ :=
    exists_doubling_coords R P hRR hP0 hPeq
  -- `T` is `2`-torsion, so its ordinate is fixed by `negY`
  have hT2' : Point.some θ u hnsT + Point.some θ u hnsT = 0 := by rw [← hTeq]; exact hT2
  have hnegT : -Point.some θ u hnsT = Point.some θ u hnsT := neg_eq_of_add_eq_zero_left hT2'
  have hu : 2 * u + (E⁄ℚ).a₁ * θ + (E⁄ℚ).a₃ = 0 := by
    have h := hnegT
    rw [Point.neg_some] at h
    have h2 := (Point.some.inj h).2
    rw [negY] at h2
    linear_combination -h2
  -- the Weierstrass equations of the four points
  have eT := hnsT.1
  have eR := hnsR.1
  have eP := hnsP.1
  have eQ := hnsQ.1
  rw [equation_iff] at eT eR eP eQ
  -- `θ` is a root of the `2`-division cubic: `(2u + a₁θ + a₃)² = 0` after
  -- clearing the equation at `(θ, u)`
  have hcubic : 4 * θ ^ 3 + ((E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂) * θ ^ 2
      + (2 * (E⁄ℚ).a₁ * (E⁄ℚ).a₃ + 4 * (E⁄ℚ).a₄) * θ
      + ((E⁄ℚ).a₃ ^ 2 + 4 * (E⁄ℚ).a₆) = 0 := by
    linear_combination (-4 : ℚ) * eT + (2 * u + (E⁄ℚ).a₁ * θ + (E⁄ℚ).a₃) * hu
  -- equal abscissae force equality or negation of the points
  have hRθ : xR ≠ θ := by
    intro hx
    rcases (Point.X_eq_iff (h₁ := hnsR) (h₂ := hnsT)).mp hx with h | h
    · exact hRT (hReq.trans (h.trans hTeq.symm))
    · exact hRT (hReq.trans ((h.trans hnegT).trans hTeq.symm))
  have hPθ : xP ≠ θ := by
    intro hx
    rcases (Point.X_eq_iff (h₁ := hnsP) (h₂ := hnsT)).mp hx with h | h
    · exact hPT (hPeq.trans (h.trans hTeq.symm))
    · exact hPT (hPeq.trans ((h.trans hnegT).trans hTeq.symm))
  have hQθ : xQ ≠ θ := by
    intro hx
    rcases (Point.X_eq_iff (h₁ := hnsQ) (h₂ := hnsT)).mp hx with h | h
    · exact hQT (hQeq.trans (h.trans hTeq.symm))
    · exact hQT (hQeq.trans ((h.trans hnegT).trans hTeq.symm))
  have hPQ : xP ≠ xQ := by
    intro hx
    rcases (Point.X_eq_iff (h₁ := hnsP) (h₂ := hnsQ)).mp hx with h | h
    · exact hPQ1 (hPeq.trans (h.trans hQeq.symm))
    · exact hPQ2 (hPeq.trans (h.trans (congrArg Neg.neg hQeq).symm))
  exact ⟨θ, xR, yR, lR, xP, yP, lP, xQ, yQ, lQ, hcubic, eR, eP, eQ,
    slR, slP, slQ, dxR, dxP, dxQ, wR, wP, hRθ, hPθ, hQθ, hPQ⟩

/-!
#### Fermat's *other* quartic theorem: see `QuarticDescent`

Mathlib has `not_fermat_42 : a ≠ 0 → b ≠ 0 → a ^ 4 + b ^ 4 ≠ c ^ 2` but **not**
its companion `x ^ 4 - y ^ 4 = z ^ 2 → x * y * z = 0`, which the `m + k` odd
branch of the descent below needs.  It is proven by Fermat's own infinite
descent in `Fermat/FLT/FreyCurve/QuarticDescent.lean`, as
`QuarticDescent.sq_ne_quartic_sub_quartic` over the helpers
`pos_sq_of_gcd_eq_one`, `pos_right_of_mul_pos`, `self_le_sq`,
`lt_of_sq_eq_add`, `lt_of_eq_quartic` and `quartic_diff_aux`.  That module is
publicly imported above, and the same theorem is what closes the level-`32`
node through `QuarticDescent.rational_point_x0ThirtyTwo`.

A byte-identical copy of that block used to live HERE as well, in the
`MazurSixteen` namespace.  It was DELETED on 2026-07-26 and its single
consumer — `not_sextic_square` below — now calls
`QuarticDescent.sq_ne_quartic_sub_quartic` directly.
-/

/-!
#### Coprimality bookkeeping for the descent

Both branches of the sextic descent factor an integer square into pairwise
coprime pieces and apply `Int.sq_of_gcd_eq_one`. The coprimality statements are
all of the form "a common prime divisor of two of the factors divides both `m`
and `k`", which contradicts `IsCoprime m k`; `isCoprime_of_dvd_prime` packages
that reduction once and for all.
-/

/-- A square has the same parity as its base (PROVEN). -/
lemma sq_emod_two (t : ℤ) : t ^ 2 % 2 = t % 2 := by
  obtain ⟨u, hu⟩ | ⟨u, hu⟩ := Int.even_or_odd t
  · subst hu; rw [show (u + u) ^ 2 = 2 * (2 * u ^ 2) by ring]; omega
  · subst hu; rw [show (2 * u + 1) ^ 2 = 2 * (2 * u ^ 2 + 2 * u) + 1 by ring]; omega

/-- A prime `q ≠ 2` does not divide `2` (PROVEN). -/
lemma not_dvd_two {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) : ¬ ((q : ℤ) ∣ 2) := by
  intro h
  have h1 : (q : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h
  have := hq.two_le
  omega

/-- A prime dividing an odd number does not divide `2` (PROVEN). -/
lemma prime_not_dvd_two_of_odd {q : ℕ} {A : ℤ} (hq : q.Prime) (hA : A % 2 = 1)
    (h : (q : ℤ) ∣ A) : ¬ ((q : ℤ) ∣ 2) := by
  refine not_dvd_two hq ?_
  rintro rfl
  have h2 : (2 : ℤ) ∣ A := by exact_mod_cast h
  omega

/-- Cancel a factor `2` from a divisibility by an odd prime (PROVEN). -/
lemma dvd_of_dvd_two_mul {p t : ℤ} (hp : Prime p) (hp2 : ¬ p ∣ 2) (h : p ∣ 2 * t) : p ∣ t :=
  (hp.dvd_mul.mp h).resolve_left hp2

/-- **Coprimality by prime divisors** (PROVEN): if every prime dividing both `A`
and `B` divides `m` and `k`, and `m`, `k` are coprime, then `A` and `B` are
coprime. -/
lemma isCoprime_of_dvd_prime {m k A B : ℤ} (hmk : IsCoprime m k)
    (H : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ A → (q : ℤ) ∣ B → ((q : ℤ) ∣ m ∧ (q : ℤ) ∣ k)) :
    IsCoprime A B := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hc
  obtain ⟨q, hq, hqA, hqB⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
  obtain ⟨h1, h2⟩ := H q hq (Int.natCast_dvd.mpr hqA) (Int.natCast_dvd.mpr hqB)
  have hu := hmk.isUnit_of_dvd' h1 h2
  rw [Int.isUnit_iff] at hu
  have := hq.two_le
  omega

/-- **The sextic descent, case `m + k` odd** (PROVEN). All three of `m² − k²`,
`m² + k²`, `m² + 2mk − k²` are then odd and pairwise coprime, so the first two
are `±` squares: `m² − k² = ±e²` and `m² + k² = c²` (the latter being positive).
Since `(m² − k²)² + (2mk)² = (m² + k²)²`, this exhibits `c⁴ − e⁴ = (2mk)²`, which
Fermat's other quartic theorem forbids for `m, k ≠ 0` and `m² ≠ k²`. -/
lemma sextic_descent_odd {m k w : ℤ} (hmk : IsCoprime m k) (hpar : (m + k) % 2 = 1)
    (hm : m ≠ 0) (hk : k ≠ 0) (hne : m ^ 2 - k ^ 2 ≠ 0)
    (heq : w ^ 2 = (m ^ 2 - k ^ 2) * ((m ^ 2 + k ^ 2) * (m ^ 2 + 2 * m * k - k ^ 2))) :
    False := by
  have hA1 : (m ^ 2 - k ^ 2) % 2 = 1 := by
    rw [Int.sub_emod, sq_emod_two, sq_emod_two, ← Int.sub_emod]; omega
  have hA2 : (m ^ 2 + k ^ 2) % 2 = 1 := by
    rw [Int.add_emod, sq_emod_two, sq_emod_two, ← Int.add_emod]; omega
  have c12 : IsCoprime (m ^ 2 - k ^ 2) (m ^ 2 + k ^ 2) := by
    refine isCoprime_of_dvd_prime hmk (fun q hq h1 h2 => ?_)
    have hnd := prime_not_dvd_two_of_odd hq hA1 h1
    have hp : Prime ((q : ℤ)) := Nat.prime_iff_prime_int.mp hq
    obtain ⟨u1, hu1⟩ := h1
    obtain ⟨u2, hu2⟩ := h2
    have hdm : (q : ℤ) ∣ m ^ 2 :=
      dvd_of_dvd_two_mul hp hnd ⟨u1 + u2, by linear_combination hu1 + hu2⟩
    have hdk : (q : ℤ) ∣ k ^ 2 :=
      dvd_of_dvd_two_mul hp hnd ⟨u2 - u1, by linear_combination hu2 - hu1⟩
    exact ⟨hp.dvd_of_dvd_pow hdm, hp.dvd_of_dvd_pow hdk⟩
  have c13 : IsCoprime (m ^ 2 - k ^ 2) (m ^ 2 + 2 * m * k - k ^ 2) := by
    refine isCoprime_of_dvd_prime hmk (fun q hq h1 h2 => ?_)
    have hnd := prime_not_dvd_two_of_odd hq hA1 h1
    have hp : Prime ((q : ℤ)) := Nat.prime_iff_prime_int.mp hq
    obtain ⟨u1, hu1⟩ := h1
    obtain ⟨u2, hu2⟩ := h2
    have hd : (q : ℤ) ∣ m * k :=
      dvd_of_dvd_two_mul hp hnd ⟨u2 - u1, by linear_combination hu2 - hu1⟩
    rcases hp.dvd_mul.mp hd with hdm | hdk
    · obtain ⟨t, ht⟩ := hdm
      have hk2 : (q : ℤ) ∣ k ^ 2 := ⟨m * t - u1, by linear_combination m * ht - hu1⟩
      exact ⟨⟨t, ht⟩, hp.dvd_of_dvd_pow hk2⟩
    · obtain ⟨t, ht⟩ := hdk
      have hm2 : (q : ℤ) ∣ m ^ 2 := ⟨u1 + k * t, by linear_combination hu1 + k * ht⟩
      exact ⟨hp.dvd_of_dvd_pow hm2, ⟨t, ht⟩⟩
  have c23 : IsCoprime (m ^ 2 + k ^ 2) (m ^ 2 + 2 * m * k - k ^ 2) := by
    refine isCoprime_of_dvd_prime hmk (fun q hq h1 h2 => ?_)
    have hnd := prime_not_dvd_two_of_odd hq hA2 h1
    have hp : Prime ((q : ℤ)) := Nat.prime_iff_prime_int.mp hq
    obtain ⟨u1, hu1⟩ := h1
    obtain ⟨u2, hu2⟩ := h2
    have key : ∀ _hdk : (q : ℤ) ∣ k, ((q : ℤ) ∣ m ∧ (q : ℤ) ∣ k) := by
      rintro ⟨t, ht⟩
      have hm2 : (q : ℤ) ∣ m ^ 2 := ⟨u1 - k * t, by linear_combination hu1 - k * ht⟩
      exact ⟨hp.dvd_of_dvd_pow hm2, ⟨t, ht⟩⟩
    have hd : (q : ℤ) ∣ k * (m - k) :=
      dvd_of_dvd_two_mul hp hnd ⟨u2 - u1, by linear_combination hu2 - hu1⟩
    rcases hp.dvd_mul.mp hd with hdk | hdmk
    · exact key hdk
    · obtain ⟨t, ht⟩ := hdmk
      have hk2 : (q : ℤ) ∣ k ^ 2 :=
        dvd_of_dvd_two_mul hp hnd ⟨u1 - t * (m + k), by linear_combination hu1 - (m + k) * ht⟩
      exact key (hp.dvd_of_dvd_pow hk2)
  obtain ⟨e, he⟩ := Int.sq_of_gcd_eq_one
    (Int.isCoprime_iff_gcd_eq_one.mp (c12.mul_right c13)) heq.symm
  obtain ⟨c, hc⟩ := Int.sq_of_gcd_eq_one
    (Int.isCoprime_iff_gcd_eq_one.mp (c12.symm.mul_right c23))
    (show (m ^ 2 + k ^ 2) * ((m ^ 2 - k ^ 2) * (m ^ 2 + 2 * m * k - k ^ 2)) = w ^ 2 by
      linear_combination -heq)
  have hmpos : (0 : ℤ) < m ^ 2 := lt_of_le_of_ne (sq_nonneg m) (Ne.symm (pow_ne_zero 2 hm))
  have hpos : (0 : ℤ) < m ^ 2 + k ^ 2 := by linarith only [hmpos, sq_nonneg k]
  have hc' : m ^ 2 + k ^ 2 = c ^ 2 := by
    rcases hc with h | h
    · exact h
    · exfalso; rw [h] at hpos; linarith only [hpos, sq_nonneg c]
  have hsq : (m ^ 2 - k ^ 2) ^ 2 = e ^ 4 := by rcases he with h | h <;> rw [h] <;> ring
  refine QuarticDescent.sq_ne_quartic_sub_quartic (x := c) (y := e) (z := 2 * m * k) ?_ ?_ ?_ ?_
  · rintro rfl
    rw [show (0 : ℤ) ^ 2 = 0 by ring] at hc'
    linarith only [hpos, hc']
  · rintro rfl
    rw [show (0 : ℤ) ^ 4 = 0 by ring] at hsq
    exact hne ((pow_eq_zero_iff two_ne_zero).mp hsq)
  · exact mul_ne_zero (mul_ne_zero two_ne_zero hm) hk
  · linear_combination (-(c ^ 2 + m ^ 2 + k ^ 2)) * hc' + hsq

/-- **The sextic descent, case `m` and `k` both odd** (PROVEN). Writing
`m = P + Q`, `k = P − Q` with `P, Q` coprime of opposite parity turns the sextic
into `w² = 16·P·Q·(P²+Q²)·(P²+2PQ−Q²)`, so `4 ∣ w` and the four factors — again
pairwise coprime — are `±` squares. From `P = ±a²`, `Q = ±b²` and `P² + Q² = c²`
one gets `a⁴ + b⁴ = c²`, which mathlib's `not_fermat_42` forbids unless `P = 0`
or `Q = 0`, i.e. `m = ∓k`. -/
lemma sextic_descent_even {m k w : ℤ} (hmk : IsCoprime m k) (hm2 : m % 2 = 1) (hk2 : k % 2 = 1)
    (hne1 : m - k ≠ 0) (hne2 : m + k ≠ 0)
    (heq : w ^ 2 = (m ^ 2 - k ^ 2) * ((m ^ 2 + k ^ 2) * (m ^ 2 + 2 * m * k - k ^ 2))) :
    False := by
  obtain ⟨P, hP⟩ : ∃ P, m + k = 2 * P := ⟨(m + k) / 2, by omega⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, m - k = 2 * Q := ⟨(m - k) / 2, by omega⟩
  have hmPQ : m = P + Q := by omega
  have hkPQ : k = P - Q := by omega
  have hPQ : IsCoprime P Q := by
    obtain ⟨u, v, huv⟩ := hmk
    refine ⟨u + v, u - v, ?_⟩
    rw [hmPQ, hkPQ] at huv; linear_combination huv
  have hpar : (P + Q) % 2 = 1 := by rw [← hmPQ]; exact hm2
  have hP0 : P ≠ 0 := fun h => hne2 (by omega)
  have hQ0 : Q ≠ 0 := fun h => hne1 (by omega)
  have heq' : w ^ 2 = 16 * (P * (Q * ((P ^ 2 + Q ^ 2) * (P ^ 2 + 2 * P * Q - Q ^ 2)))) := by
    rw [hmPQ, hkPQ] at heq; linear_combination heq
  obtain ⟨w1, hw1⟩ : (2 : ℤ) ∣ w := by
    refine Int.Prime.dvd_pow' (k := 2) Nat.prime_two ?_
    refine ⟨8 * (P * (Q * ((P ^ 2 + Q ^ 2) * (P ^ 2 + 2 * P * Q - Q ^ 2)))), ?_⟩
    push_cast; linear_combination heq'
  have heq2 : w1 ^ 2 = 4 * (P * (Q * ((P ^ 2 + Q ^ 2) * (P ^ 2 + 2 * P * Q - Q ^ 2)))) := by
    apply mul_left_cancel₀ (show (4 : ℤ) ≠ 0 by norm_num)
    rw [hw1] at heq'; linear_combination heq'
  obtain ⟨v, hv⟩ : (2 : ℤ) ∣ w1 := by
    refine Int.Prime.dvd_pow' (k := 2) Nat.prime_two ?_
    refine ⟨2 * (P * (Q * ((P ^ 2 + Q ^ 2) * (P ^ 2 + 2 * P * Q - Q ^ 2)))), ?_⟩
    push_cast; linear_combination heq2
  have heqv : v ^ 2 = P * (Q * ((P ^ 2 + Q ^ 2) * (P ^ 2 + 2 * P * Q - Q ^ 2))) := by
    apply mul_left_cancel₀ (show (4 : ℤ) ≠ 0 by norm_num)
    rw [hv] at heq2; linear_combination heq2
  have hB3odd : (P ^ 2 + Q ^ 2) % 2 = 1 := by
    rw [Int.add_emod, sq_emod_two, sq_emod_two, ← Int.add_emod]; omega
  have d13 : IsCoprime P (P ^ 2 + Q ^ 2) := by
    refine isCoprime_of_dvd_prime hPQ (fun q hq h1 h2 => ?_)
    have hp : Prime ((q : ℤ)) := Nat.prime_iff_prime_int.mp hq
    obtain ⟨t, ht⟩ := h1
    obtain ⟨u2, hu2⟩ := h2
    have hQ2 : (q : ℤ) ∣ Q ^ 2 := ⟨u2 - t * P, by linear_combination hu2 - P * ht⟩
    exact ⟨⟨t, ht⟩, hp.dvd_of_dvd_pow hQ2⟩
  have d14 : IsCoprime P (P ^ 2 + 2 * P * Q - Q ^ 2) := by
    refine isCoprime_of_dvd_prime hPQ (fun q hq h1 h2 => ?_)
    have hp : Prime ((q : ℤ)) := Nat.prime_iff_prime_int.mp hq
    obtain ⟨t, ht⟩ := h1
    obtain ⟨u2, hu2⟩ := h2
    have hQ2 : (q : ℤ) ∣ Q ^ 2 :=
      ⟨t * P + 2 * t * Q - u2, by linear_combination P * ht + 2 * Q * ht - hu2⟩
    exact ⟨⟨t, ht⟩, hp.dvd_of_dvd_pow hQ2⟩
  have d23 : IsCoprime Q (P ^ 2 + Q ^ 2) := by
    refine isCoprime_of_dvd_prime hPQ.symm (fun q hq h1 h2 => ?_)
    have hp : Prime ((q : ℤ)) := Nat.prime_iff_prime_int.mp hq
    obtain ⟨t, ht⟩ := h1
    obtain ⟨u2, hu2⟩ := h2
    have hP2 : (q : ℤ) ∣ P ^ 2 := ⟨u2 - t * Q, by linear_combination hu2 - Q * ht⟩
    exact ⟨⟨t, ht⟩, hp.dvd_of_dvd_pow hP2⟩
  have d24 : IsCoprime Q (P ^ 2 + 2 * P * Q - Q ^ 2) := by
    refine isCoprime_of_dvd_prime hPQ.symm (fun q hq h1 h2 => ?_)
    have hp : Prime ((q : ℤ)) := Nat.prime_iff_prime_int.mp hq
    obtain ⟨t, ht⟩ := h1
    obtain ⟨u2, hu2⟩ := h2
    have hP2 : (q : ℤ) ∣ P ^ 2 :=
      ⟨u2 - 2 * P * t + t * Q, by linear_combination hu2 - 2 * P * ht + Q * ht⟩
    exact ⟨⟨t, ht⟩, hp.dvd_of_dvd_pow hP2⟩
  have d34 : IsCoprime (P ^ 2 + Q ^ 2) (P ^ 2 + 2 * P * Q - Q ^ 2) := by
    refine isCoprime_of_dvd_prime hPQ (fun q hq h1 h2 => ?_)
    have hnd := prime_not_dvd_two_of_odd hq hB3odd h1
    have hp : Prime ((q : ℤ)) := Nat.prime_iff_prime_int.mp hq
    obtain ⟨u1, hu1⟩ := h1
    obtain ⟨u2, hu2⟩ := h2
    have key : ∀ _hdq : (q : ℤ) ∣ Q, ((q : ℤ) ∣ P ∧ (q : ℤ) ∣ Q) := by
      rintro ⟨t, ht⟩
      have hP2 : (q : ℤ) ∣ P ^ 2 := ⟨u1 - t * Q, by linear_combination hu1 - Q * ht⟩
      exact ⟨hp.dvd_of_dvd_pow hP2, ⟨t, ht⟩⟩
    have hd : (q : ℤ) ∣ Q * (P - Q) :=
      dvd_of_dvd_two_mul hp hnd ⟨u2 - u1, by linear_combination hu2 - hu1⟩
    rcases hp.dvd_mul.mp hd with hdq | hdpq
    · exact key hdq
    · obtain ⟨t, ht⟩ := hdpq
      have hQ2 : (q : ℤ) ∣ Q ^ 2 :=
        dvd_of_dvd_two_mul hp hnd ⟨u1 - t * (P + Q), by linear_combination hu1 - (P + Q) * ht⟩
      exact key (hp.dvd_of_dvd_pow hQ2)
  obtain ⟨a, ha⟩ := Int.sq_of_gcd_eq_one
    (Int.isCoprime_iff_gcd_eq_one.mp (hPQ.mul_right (d13.mul_right d14))) heqv.symm
  obtain ⟨b, hb⟩ := Int.sq_of_gcd_eq_one
    (Int.isCoprime_iff_gcd_eq_one.mp (hPQ.symm.mul_right (d23.mul_right d24)))
    (show Q * (P * ((P ^ 2 + Q ^ 2) * (P ^ 2 + 2 * P * Q - Q ^ 2))) = v ^ 2 by
      linear_combination -heqv)
  obtain ⟨cc, hcc⟩ := Int.sq_of_gcd_eq_one
    (Int.isCoprime_iff_gcd_eq_one.mp (d13.symm.mul_right (d23.symm.mul_right d34)))
    (show (P ^ 2 + Q ^ 2) * (P * (Q * (P ^ 2 + 2 * P * Q - Q ^ 2))) = v ^ 2 by
      linear_combination -heqv)
  have hPpos : (0 : ℤ) < P ^ 2 := lt_of_le_of_ne (sq_nonneg P) (Ne.symm (pow_ne_zero 2 hP0))
  have hpos : (0 : ℤ) < P ^ 2 + Q ^ 2 := by linarith only [hPpos, sq_nonneg Q]
  have hcc' : P ^ 2 + Q ^ 2 = cc ^ 2 := by
    rcases hcc with h | h
    · exact h
    · exfalso; rw [h] at hpos; linarith only [hpos, sq_nonneg cc]
  have hP2 : P ^ 2 = a ^ 4 := by rcases ha with h | h <;> rw [h] <;> ring
  have hQ2 : Q ^ 2 = b ^ 4 := by rcases hb with h | h <;> rw [h] <;> ring
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [show (0 : ℤ) ^ 4 = 0 by ring] at hP2
    exact hP0 ((pow_eq_zero_iff two_ne_zero).mp hP2)
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [show (0 : ℤ) ^ 4 = 0 by ring] at hQ2
    exact hQ0 ((pow_eq_zero_iff two_ne_zero).mp hQ2)
  exact not_fermat_42 (c := cc) ha0 hb0 (by linear_combination -hP2 - hQ2 + hcc')

/-- **No rational square on the sextic model of `X_1(16)`** (PROVEN 2026-07-25 —
a classical descent, entirely elementary, over Fermat's two quartic theorems).

For `n ∉ {0, 1, −1}` the value `(n²−1)(n²+1)(n²+2n−1)` is not a rational
square. Geometrically: the only rational points of `X_1(16)` are its
cusps.

**The descent, in full.** Write `n = m/k` in lowest terms and clear
denominators: a rational square makes
`W² = (m−k)(m+k)(m²+k²)(m²+2mk−k²)` for an integer `W` (the rational
`W = Y·k³` is an integer because `ℤ` is integrally closed). Now split on
the parity of `m + k`.

*Case `m + k` odd* (`sextic_descent_odd`). All four factors are odd, and
each pair has gcd dividing `2`, hence gcd `1`: they are pairwise coprime, so
each is `±` a square (`Int.sq_of_gcd_eq_one`). Only two are needed:
`m² − k² = ±e²` and `m² + k² = c²` (the latter positive). Since
`(m²−k²)² + (2mk)² = (m²+k²)²`, this reads `c⁴ − e⁴ = (2mk)²`, and Fermat's
*other* quartic theorem `QuarticDescent.sq_ne_quartic_sub_quartic` forces
`c e · 2mk = 0`;
`c ≠ 0` and `e ≠ 0` hold because `m² + k² > 0` and `m ≠ ±k`, so `mk = 0` —
excluded.

*Case `m + k` even, i.e. `m, k` both odd* (`sextic_descent_even`). Put
`p = (m+k)/2`, `q = (m−k)/2`, so `m = p+q`, `k = p−q`, `gcd(p,q) = 1` and
`p, q` have opposite parity. Then `m²−k² = 4pq`, `m²+k² = 2(p²+q²)` and
`m²+2mk−k² = 2(p²+2pq−q²)`, so `W² = 16·pq(p²+q²)(p²+2pq−q²)` and
`4 ∣ W`. The four factors `p`, `q`, `p²+q²`, `p²+2pq−q²` are pairwise
coprime, so `p = ε₁a²`, `q = ε₂b²`, `p²+q² = c²`, giving
`a⁴ + b⁴ = c²`. Mathlib's `not_fermat_42` forces `ab = 0`, i.e. `p = 0`
or `q = 0`, i.e. `m = ±k` — excluded.

**The mathlib gap, now filled here.** Mathlib's
`Mathlib/NumberTheory/FLT/Four.lean` has only
`not_fermat_42 : a ≠ 0 → b ≠ 0 → a⁴ + b⁴ ≠ c²`. Fermat's *other* quartic
theorem `x⁴ − y⁴ = z² → xyz = 0` is genuinely absent, and is proved in the
publicly imported `Fermat/FLT/FreyCurve/QuarticDescent.lean` as
`QuarticDescent.sq_ne_quartic_sub_quartic`, by an independent infinite
descent. It is what the first case needs; note it cannot be
strengthened, since `x = y, z = 0` and `y = 0, z = x²` are solutions.

**The exclusions are sharp.** A search over the ~320k coprime pairs with
`|m|, k ≤ 300` (PARI/GP, 2026-07-25) finds exactly `(m,k) ∈ {(0,1), (1,1),
(−1,1)}`, i.e. `n ∈ {0, 1, −1}`, and those three DO make the sextic a
square: they are the cusps, and the statement is false without them. -/
theorem not_sextic_square (n Y : ℚ) (h0 : n ≠ 0) (h1 : n ≠ 1) (hm1 : n ≠ -1) :
    Y ^ 2 ≠ (n ^ 2 - 1) * (n ^ 2 + 1) * (n ^ 2 + 2 * n - 1) := by
  intro hY
  -- write `n = m / k` in lowest terms
  obtain ⟨m, k, hkpos, hcop, hn⟩ :
      ∃ m k : ℤ, 0 < k ∧ IsCoprime m k ∧ n * (k : ℚ) = (m : ℚ) := by
    refine ⟨n.num, (n.den : ℤ), by exact_mod_cast n.pos, ?_, ?_⟩
    · rw [Int.isCoprime_iff_gcd_eq_one]
      simpa [Int.gcd] using n.reduced
    · have hden : ((n.den : ℚ)) ≠ 0 := by exact_mod_cast n.den_nz
      push_cast
      exact ((div_eq_iff hden).mp (Rat.num_div_den n)).symm
  have hkQ : ((k : ℚ)) ≠ 0 := by exact_mod_cast hkpos.ne'
  have hk0 : k ≠ 0 := hkpos.ne'
  -- the three excluded values of `n` become `m ≠ 0` and `m ≠ ±k`
  have hm0 : m ≠ 0 := by
    intro h; apply h0
    have hz : n * (k : ℚ) = 0 := by rw [hn, h]; norm_num
    exact (mul_eq_zero.mp hz).resolve_right hkQ
  have hmk1 : m ≠ k := by
    intro h; apply h1
    have hz : n * (k : ℚ) = 1 * (k : ℚ) := by rw [hn, h]; ring
    exact mul_right_cancel₀ hkQ hz
  have hmk2 : m ≠ -k := by
    intro h; apply hm1
    have hz : n * (k : ℚ) = (-1) * (k : ℚ) := by rw [hn, h]; push_cast; ring
    exact mul_right_cancel₀ hkQ hz
  -- clear denominators: `W = Y k³` satisfies an integral equation
  have hW : (Y * (k : ℚ) ^ 3) ^ 2 =
      (((m ^ 2 - k ^ 2) * ((m ^ 2 + k ^ 2) * (m ^ 2 + 2 * m * k - k ^ 2)) : ℤ) : ℚ) := by
    push_cast
    rw [← hn]
    linear_combination (k : ℚ) ^ 6 * hY
  -- `W` is an integer, because its square is one and `(q ^ 2).den = q.den ^ 2`
  have hden1 : (Y * (k : ℚ) ^ 3).den = 1 := by
    have h2 : ((Y * (k : ℚ) ^ 3) ^ 2).den = 1 := by rw [hW]; exact Rat.den_intCast _
    rw [Rat.den_pow] at h2
    exact (Nat.pow_eq_one.mp h2).resolve_right (by norm_num)
  obtain ⟨w, hw⟩ : ∃ w : ℤ, Y * (k : ℚ) ^ 3 = (w : ℚ) :=
    ⟨(Y * (k : ℚ) ^ 3).num, ((Rat.den_eq_one_iff _).mp hden1).symm⟩
  have hwint : w ^ 2 = (m ^ 2 - k ^ 2) * ((m ^ 2 + k ^ 2) * (m ^ 2 + 2 * m * k - k ^ 2)) := by
    have h3 : ((w : ℚ)) ^ 2 =
        (((m ^ 2 - k ^ 2) * ((m ^ 2 + k ^ 2) * (m ^ 2 + 2 * m * k - k ^ 2)) : ℤ) : ℚ) := by
      rw [← hw]; exact hW
    exact_mod_cast h3
  -- split on the parity of `m + k`
  rcases Int.emod_two_eq_zero_or_one (m + k) with hpar | hpar
  · have hnb : ¬((2 : ℤ) ∣ m ∧ (2 : ℤ) ∣ k) := by
      rintro ⟨d1, d2⟩
      have hu := hcop.isUnit_of_dvd' d1 d2
      rw [Int.isUnit_iff] at hu
      omega
    have hmo : m % 2 = 1 := by
      rcases Int.emod_two_eq_zero_or_one m with h | h
      · exact absurd ⟨Int.dvd_of_emod_eq_zero h, Int.dvd_of_emod_eq_zero (by omega)⟩ hnb
      · exact h
    have hko : k % 2 = 1 := by omega
    exact sextic_descent_even hcop hmo hko (sub_ne_zero.mpr hmk1)
      (fun h => hmk2 (by omega)) hwint
  · refine sextic_descent_odd hcop hpar hm0 hk0 ?_ hwint
    intro h
    have hfac : (m - k) * (m + k) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hfac with h' | h'
    · exact hmk1 (by omega)
    · exact hmk2 (by omega)

/-- **A rational point of order `16` puts a rational point on `X_1(16)`**
(PROVEN from `exists_chain_coords` and the algebra above): the geometric
half of the level-`16` node. -/
theorem exists_sextic_point (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P R : (E⁄ℚ).Point) (hP : addOrderOf P = 8) (hR : (2 : ℕ) • R = P) :
    ∃ n Y : ℚ, n ≠ 0 ∧ n ≠ 1 ∧ n ≠ -1 ∧
      Y ^ 2 = (n ^ 2 - 1) * (n ^ 2 + 1) * (n ^ 2 + 2 * n - 1) := by
  obtain ⟨θ, xR, yR, lR, xP, yP, lP, xQ, yQ, lQ, hθ, eR, eP, eQ,
    slR, slP, slQ, dxR, dxP, dxQ, wR, wP, hRθ, hPθ, hQθ, hPQ⟩ :=
      exists_chain_coords E P R hP hR
  -- pass to short form: complete the square, translate `θ` to the origin
  have hcR := shift_equation (θ := θ) eR hθ
  have hcP := shift_equation (θ := θ) eP hθ
  have hcQ := shift_equation (θ := θ) eQ hθ
  have dR := doubling_short hcR (shift_slope (θ := θ) slR)
    (shift_addX.trans (by rw [dxR]))
  have dP := doubling_short hcP (shift_slope (θ := θ) slP)
    (shift_addX.trans (by rw [dxP]))
  have dQ0 := doubling_short hcQ (shift_slope (θ := θ) slQ)
    (shift_addX.trans (by rw [dxQ]))
  -- the chain ends at the origin, so `X_Q² = b`
  have dQ : (xQ - θ) ^ 2 =
      3 * θ ^ 2 + ((E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂) / 2 * θ
        + (2 * (E⁄ℚ).a₄ + (E⁄ℚ).a₁ * (E⁄ℚ).a₃) / 2 := by
    have h0 : ((xQ - θ) ^ 2 - (3 * θ ^ 2 + ((E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂) / 2 * θ
        + (2 * (E⁄ℚ).a₄ + (E⁄ℚ).a₁ * (E⁄ℚ).a₃) / 2)) ^ 2 = 0 := by
      rw [← dQ0]; ring
    have h1 := sq_eq_zero_iff.mp h0
    linarith
  exact sextic_of_short_chain hcR hcP hcQ dR dP dQ
    (fun h => wR (by linarith)) (fun h => wP (by linarith))
    (sub_ne_zero.mpr hRθ) (sub_ne_zero.mpr hPθ) (sub_ne_zero.mpr hQθ)
    (fun h => hPQ (by linarith))

end MazurSixteen

/-- **No rational point of order `8` that is twice a rational point**
(PROVEN — the `X_1(16)` content in its descent form): if
`P ∈ E(ℚ)` has order `8` then `P ∉ 2 · E(ℚ)`. This is exactly the
statement that the degree-`2` covering `X_1(16) → X_1(8)` — halving the
level-`8` point — has no non-cuspidal rational point in its image;
`X_1(16)` has genus `2` (recomputed 2026-07-25: `μ/12 = 8`, `14` cusps,
so `g = 1 + 8 − 7 = 2`) and no non-cuspidal rational point
(Kenku–Ligozat–Kubert; subsumed in Mazur 1977, Thm 8).

**AUDIT SUPERSEDED 2026-07-25 (later the same day): this node is NOT
irreducible, and is now DERIVED** from the two elementary leaves
`MazurSixteen.exists_chain_coords` and `MazurSixteen.not_sextic_square`
via `MazurSixteen.exists_sextic_point`. The "genus-`2` curve plus
Chabauty" assessment recorded below is wrong: an explicit affine model of
`X_1(16)` — the sextic `(n²−1)(n²+1)(n²+2n−1)` — is reachable by pure
field algebra from the duplication formula in short Weierstrass form, and
its rational points fall to a classical two-case descent needing only
Fermat's quartic theorems. See the section note above this declaration for
the full route. The paragraphs below are retained as the historical audit.

Equivalent to
`no_torsion_order_16` below — a halving `R` of an order-`8` point
necessarily has order `16`, since `addOrderOf (2 • R) = 8` forces
`addOrderOf R = 16` — but stated over the genus-`0` level `8`, where the
Tate normal form `b = (2d − 1)(d − 1)`, `c = b/d` is explicit, so that
the only missing ingredient is the halving condition. Routes checked and
rejected:

* *The elementary halving criterion behind `not_full_four_torsion_rat`
  does not reach this level.* A point of order `16` makes ONE `2`-torsion
  abscissa `4`-divisible, giving a single square condition rather than
  the three simultaneous ones that the sign argument needs.
* *The `X_0` / isogeny shortcut is NOT available here.* `16` is a
  rational cyclic isogeny degree: `[1,−1,0,0,−5]` of conductor `45` has
  isogeny-degree set `{1, 2, 4, 8, 16}` (PARI/GP `ellisomat`, witness
  recomputed 2026-07-25), so `X_0(16)` has non-cuspidal rational points.
* *Divisor reduction fails by design.* The proper divisors `1, 2, 4, 8`
  all lie in Mazur's allowed set.
* *Reduction plus Hasse only bounds the conductor.* `16 ∣ #Ẽ(𝔽_p)` at
  every odd prime `p` of good reduction, and `p + 1 + 2√p < 16` for
  `p ≤ 7`, forcing bad reduction at `3, 5, 7` (`105 ∣ N_E`); `p = 2`
  gives nothing at all, the odd part of `ℤ/16` being trivial.

A formal proof needs the genus-`2` curve `X_1(16)` and a determination
of its rational points (Ogg's descent, or Chabauty on its Jacobian).
Note that the hypothesis cannot be weakened to `addOrderOf P = 8` alone:
points of order `8` are permitted by Mazur's list, and the whole content
of the node is that no such point is halvable over `ℚ`. -/
theorem WeierstrassCurve.not_halved_order_eight_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (P R : (E⁄ℚ).Point)
    (hP : addOrderOf P = 8) (hR : (2 : ℕ) • R = P) : False := by
  obtain ⟨n, Y, h0, h1, hm1, hY⟩ := MazurSixteen.exists_sextic_point E P R hP hR
  exact MazurSixteen.not_sextic_square n Y h0 h1 hm1 hY

/-- **No rational point of order `16`** (DERIVED 2026-07-25 from the
descent-form leaf `not_halved_order_eight_point`): a point `Q` of order
`16` exhibits the order-`8` point `2 • Q` as twice a rational point.
`X_1(16)` has genus `2` and no non-cuspidal rational point
(Kenku–Ligozat–Kubert; subsumed in Mazur 1977, Thm 8). -/
theorem WeierstrassCurve.no_torsion_order_16 (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (Q : (E⁄ℚ).Point) : addOrderOf Q ≠ 16 := by
  intro hQ
  refine E.not_halved_order_eight_point ((2 : ℕ) • Q) Q ?_ rfl
  rw [addOrderOf_nsmul' Q (by decide), hQ]; decide

/-!
#### `X_1(18)`, cut down to one explicit Diophantine leaf (2026-07-25)

This block replaces the bare `X_1(18)` citation by an EXPLICIT plane
model, so that what is left open is a concrete polynomial statement
rather than "a modular curve has no non-cuspidal rational point".
EXACTLY ONE leaf remains — `MazurLevel18.no_rational_point_on_X18`,
the actual `X_1(18)` content, now a statement about one explicit
polynomial in two rational unknowns. Everything else is PROVEN here,
including the reduction to normal form
(`WeierstrassCurve.exists_tateNormalForm_of_order_nine`) and, since
2026-07-25, the `2`-descent step `no_rational_two_torsion_abscissa`
that replaces the `2`-torsion abscissa `x` by the square root
`s = ((1 − c)x − b)/(2xc)` of `(b − x)/c²`, cutting the plane model from
total degree `8` to total degree `6`.

The chain, all PROVEN below. Write the Tate normal form
`E(b,c) : y² + (1 − c)xy − by = x³ − bx²` with `P = (0,0)`; the group
law gives `2P = (b, bc)` and `3P = (c, b − c)` (`tate_triple`).
`P` has order `9` exactly when `3P` has order `3`, and doubling
`3P` onto `−3P` is one equation, which expands to
`ψ₃(c) = c⁵ + c⁴ + (1 − b)c³ − 3bc² + 3b²c − b³ = 0` (`psi3_eq_zero`).
That curve is rational: `d := c²/(b − c)` inverts the classical
`c = d²(d − 1)`, `b = c(d² − d + 1)` (`exists_param` — both identities
have numerator exactly `ψ₃(c)`, so each is one `linear_combination`).
Along it the discriminant is
`Δ = d⁹(d − 1)⁹(d² − d + 1)³(d³ − 6d² + 3d + 1)` (`delta_param`), which
pins the degenerate locus. Finally a rational `2`-torsion point is a
rational root of the `2`-division cubic (`two_division_cubic`), and
that root is the second coordinate of the genus-`2` curve.
-/

namespace MazurLevel18

variable {W : WeierstrassCurve.Affine ℚ}

/-- **A rational `2`-torsion point is a root of the `2`-division cubic**
(PROVEN — pure algebra): a point `(x, y)` on `W` with
`y = negY x y` (the characterisation of `2`-torsion, Silverman AEC
III.2.3) has `4x³ + b₂x² + 2b₄x + b₆ = 0`, because
`(2y + a₁x + a₃)² = 4x³ + b₂x² + 2b₄x + b₆` on the curve and the left
side vanishes. -/
lemma two_division_cubic {x y : ℚ} (heq : W.Equation x y) (hy : y = W.negY x y) :
    4 * x ^ 3 + (W.a₁ ^ 2 + 4 * W.a₂) * x ^ 2 + 2 * (2 * W.a₄ + W.a₁ * W.a₃) * x
      + (W.a₃ ^ 2 + 4 * W.a₆) = 0 := by
  rw [Affine.equation_iff] at heq
  rw [Affine.negY] at hy
  linear_combination (2 * y + W.a₁ * x + W.a₃) * hy - 4 * heq

/-- **`a₂ = 0` in the partial normal form means `(0,0)` has order `3`**
(PROVEN): on a curve with `a₂ = a₄ = 0` and `a₃ ≠ 0`, the tangent at
`(0,0)` is horizontal, so the slope there is `0` and
`x(2•(0,0)) = −a₂ = 0 = x((0,0))`; since `(0,0) ≠ 0` this forces
`2•(0,0) = −(0,0)`. This is the step that makes the final scaling of
the Tate normal form legitimate: it is exactly why `a₂ ≠ 0` once the
point has order `9`. -/
lemma order_three_of_a₂_eq_zero (h2 : W.a₂ = 0) (h4 : W.a₄ = 0) (h3ne : W.a₃ ≠ 0)
    (hns : W.Nonsingular 0 0) :
    Point.some 0 0 hns + Point.some 0 0 hns + Point.some 0 0 hns = 0 := by
  have hn0 : W.negY 0 0 = -W.a₃ := by rw [Affine.negY]; ring
  have hy0 : (0 : ℚ) ≠ W.negY 0 0 := by
    rw [hn0]; intro h; exact h3ne (by linarith [h])
  have hL : W.slope 0 0 0 0 = 0 := by
    rw [Affine.slope_of_Y_ne rfl hy0, h4]; simp
  have hdbl : Point.some 0 0 hns + Point.some 0 0 hns = -Point.some 0 0 hns := by
    rw [Point.add_self_of_Y_ne hy0, Point.neg_some hns]
    exact Point.some_eq_some W (by simp only [Affine.addX, hL, h2]; ring)
      (by simp only [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY, hL, h2]; ring)
  rw [hdbl]; abel

section Tate

variable {b c : ℚ}
  (h1 : W.a₁ = 1 - c) (h2 : W.a₂ = -b) (h3 : W.a₃ = -b) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0)

include h3 h6 in
/-- `(0,0)` is a nonsingular point of a curve in Tate normal form: it is
on the curve because `a₆ = 0`, and nonsingular because `a₃ = -b ≠ 0`. -/
lemma nonsingular_zero_zero (hb : b ≠ 0) : W.Nonsingular 0 0 :=
  Affine.nonsingular_zero.mpr ⟨h6, Or.inl (by rw [h3]; exact neg_ne_zero.mpr hb)⟩

include h3 in
/-- `−(0,0) = (0, b)` in Tate normal form. -/
lemma negY_zero_zero : W.negY 0 0 = b := by
  rw [Affine.negY, h3]; ring

include h1 h2 h3 h4 in
/-- **`3 • (0,0) = (c, b − c)`** (PROVEN — two applications of the
group law). The tangent at `(0,0)` is horizontal (`a₄ = 0`), so the
slope is `0` and `2•(0,0) = (b, bc)`; the chord from `(b, bc)` to
`(0,0)` has slope `c`, giving `3•(0,0) = (c, b − c)`. These are the
classical Tate-normal-form values. -/
lemma tate_triple (hb : b ≠ 0) (hns : W.Nonsingular 0 0) :
    ∃ (x₃ y₃ : ℚ) (h₃ : W.Nonsingular x₃ y₃),
      Point.some 0 0 hns + Point.some 0 0 hns + Point.some 0 0 hns = Point.some x₃ y₃ h₃ ∧
        x₃ = c ∧ y₃ = b - c := by
  have hn0 : W.negY 0 0 = b := negY_zero_zero h3
  have hy0 : (0 : ℚ) ≠ W.negY 0 0 := by rw [hn0]; exact fun h => hb h.symm
  have hL : W.slope 0 0 0 0 = 0 := by
    rw [Affine.slope_of_Y_ne rfl hy0, h4]; simp
  -- the doubling, with its coordinates made opaque so that no rewrite
  -- has to fight the dependent nonsingularity argument
  obtain ⟨x₂, y₂, h₂, hdbl, hx₂, hy₂⟩ :
      ∃ (x₂ y₂ : ℚ) (h₂ : W.Nonsingular x₂ y₂),
        Point.some 0 0 hns + Point.some 0 0 hns = Point.some x₂ y₂ h₂ ∧
          x₂ = b ∧ y₂ = b * c :=
    ⟨_, _, _, Point.add_self_of_Y_ne hy0, by simp only [Affine.addX, hL, h2]; ring,
      by simp only [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY, hL, h1, h2, h3]; ring⟩
  have hx₂ne : x₂ ≠ 0 := by rw [hx₂]; exact hb
  have hL3 : W.slope x₂ 0 y₂ 0 = c := by
    rw [Affine.slope_of_X_ne hx₂ne, hx₂, hy₂]; field_simp; ring
  refine ⟨_, _, _, by rw [hdbl, Point.add_of_X_ne hx₂ne], ?_, ?_⟩
  · rw [hL3]; simp only [Affine.addX, hx₂, h1, h2]; ring
  · rw [hL3]
    simp only [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY, hx₂, hy₂, h1, h2, h3]
    ring

include h1 h2 h3 h4 in
/-- **The order-`9` condition in Tate normal form is `ψ₃(c) = 0`**
(PROVEN). If `9 • (0,0) = 0` then `R := 3•(0,0) = (c, b − c)` satisfies
`3R = 0`, so `R + R = −R`; `R` is not `2`-torsion (else `R = 0`), so
the doubling slope `M = N/D` is defined with `N = 2c² − bc − b + c`
and `D = b − c − c²`, and `addX c c M = c` clears to
`N² + (1 − c)ND + (b − 3c)D² = 0`, which is `−ψ₃(c)`. -/
lemma psi3_eq_zero (hb : b ≠ 0) (hns : W.Nonsingular 0 0)
    (h9 : (9 : ℕ) • Point.some 0 0 hns = 0) :
    c ^ 5 + c ^ 4 + (1 - b) * c ^ 3 - 3 * b * c ^ 2 + 3 * b ^ 2 * c - b ^ 3 = 0 := by
  obtain ⟨x₃, y₃, h₃, hR, hx₃, hy₃⟩ := tate_triple h1 h2 h3 h4 hb hns
  have hRRR : Point.some x₃ y₃ h₃ + Point.some x₃ y₃ h₃ + Point.some x₃ y₃ h₃ = 0 := by
    rw [← hR, ← h9]; abel
  have hRR : Point.some x₃ y₃ h₃ + Point.some x₃ y₃ h₃ = -Point.some x₃ y₃ h₃ :=
    add_eq_zero_iff_eq_neg.mp hRRR
  have hne : y₃ ≠ W.negY x₃ y₃ := by
    intro h
    have h0 : Point.some x₃ y₃ h₃ + Point.some x₃ y₃ h₃ = 0 := Point.add_self_of_Y_eq h
    rw [h0] at hRR
    exact Point.some_ne_zero _ (neg_eq_zero.mp hRR.symm)
  have hD : y₃ - W.negY x₃ y₃ = b - c - c ^ 2 := by
    rw [Affine.negY, h1, h3, hx₃, hy₃]; ring
  have hDne : b - c - c ^ 2 ≠ 0 := by rw [← hD]; exact sub_ne_zero.mpr hne
  have hM : W.slope x₃ x₃ y₃ y₃ = (2 * c ^ 2 - b * c - b + c) / (b - c - c ^ 2) := by
    rw [Affine.slope_of_Y_ne rfl hne, hD, hx₃, hy₃, h1, h2, h4]
    rw [div_eq_div_iff hDne hDne]; ring
  have hcond : W.addX x₃ x₃ (W.slope x₃ x₃ y₃ y₃) = x₃ :=
    (Point.some.inj ((Point.add_self_of_Y_ne (h₁ := h₃) hne).symm.trans
      (hRR.trans (Point.neg_some h₃)))).1
  rw [Affine.addX, hM, hx₃, h1, h2] at hcond
  have hpoly : (2 * c ^ 2 - b * c - b + c) ^ 2
      + (1 - c) * (2 * c ^ 2 - b * c - b + c) * (b - c - c ^ 2)
      + (b - 3 * c) * (b - c - c ^ 2) ^ 2 = 0 := by
    field_simp at hcond
    linear_combination hcond
  linear_combination -hpoly

end Tate

/-- **The `X_1(9)` parametrization is birational** (PROVEN): on
`ψ₃(c) = 0` the classical Kubert parameter is recovered as
`d = c²/(b − c)`. Both `c − d²(d − 1)` and `b − c(d² − d + 1)` have
numerator exactly `ψ₃(c)` (times `c` in the first case), so each is a
single `linear_combination`. The excluded case `b = c` forces `c⁵ = 0`,
hence `c = 0`, which is degenerate. -/
lemma exists_param {b c : ℚ} (hc : c ≠ 0)
    (h9 : c ^ 5 + c ^ 4 + (1 - b) * c ^ 3 - 3 * b * c ^ 2 + 3 * b ^ 2 * c - b ^ 3 = 0) :
    ∃ d : ℚ, c = d ^ 2 * (d - 1) ∧ b = c * (d ^ 2 - d + 1) := by
  have hbc : b - c ≠ 0 := by
    intro h
    have hb' : b = c := by linarith [sub_eq_zero.mp h]
    rw [hb'] at h9
    exact hc (pow_eq_zero_iff (n := 5) (by norm_num) |>.mp (by linear_combination h9))
  refine ⟨c ^ 2 / (b - c), ?_, ?_⟩
  · field_simp
    linear_combination -h9
  · field_simp
    linear_combination -h9

/-- **The discriminant along the `X_1(9)` line** (PROVEN):
`Δ(E(b,c)) = d⁹(d − 1)⁹(d² − d + 1)³(d³ − 6d² + 3d + 1)`. Since
`d² − d + 1` has no rational root, nondegeneracy is exactly
`d ∉ {0, 1}` together with `d³ − 6d² + 3d + 1 ≠ 0` — the cusps of
`X_1(9)`. (Numerical check: `d = 2` gives `Δ = −124416`, matching
PARI/GP `elldisc` on `[−3, −12, −12, 0, 0]`.) -/
lemma delta_param {b c : ℚ} (d : ℚ) (hc : c = d ^ 2 * (d - 1))
    (hb : b = c * (d ^ 2 - d + 1)) :
    (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve ℚ).Δ
      = d ^ 9 * (d - 1) ^ 9 * (d ^ 2 - d + 1) ^ 3 * (d ^ 3 - 6 * d ^ 2 + 3 * d + 1) := by
  subst hb; subst hc
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

/-- **`X_1(18)` HAS NO NON-CUSPIDAL RATIONAL POINT — the surviving leaf,
in its descended plane model** (sorry node; restated 2026-07-25 over the
`2`-descent coordinate `s`, which is where every known proof starts).

THE STATEMENT. Writing `c = d²(d − 1)` and `e = d² − d + 1` for the
level-`9` Tate family, the plane curve

    (2s + 1)·(c·s² − e) = s²,   i.e.
    (2s + 1)·(d²(d − 1)s² − (d² − d + 1)) = s²

has no rational point with `d ∉ {0, 1}` and `d³ − 6d² + 3d + 1 ≠ 0`.

THIS CURVE IS `X_1(18)`. It is birational to the `(d, x)` curve of the
previous cut — `x` the abscissa of the rational `2`-torsion point —
under `s = ((1 − c)x − b)/(2xc)`, `x = b − c²s²`; that birational
identification is PROVEN, it is exactly
`no_rational_two_torsion_abscissa` below. Its genus is `2`, computed
twice and independently (Singular `normal.lib::genus`; Magma `Genus`),
matching the modular computation `μ/12 = 9`, `16` cusps,
`g = 1 + 9 − 8 = 2`.

WHERE `s` COMES FROM, and why this is the right coordinate. The
`2`-division cubic is a difference of squares,

    4x³ + ((1−c)² − 4b)x² − 2b(1−c)x + b² = ((1−c)x − b)² − 4x²(b − x)

(`ring`), so a rational `2`-torsion abscissa forces `b − x` to be a
SQUARE — that is the first descent step of any treatment of this curve,
and `s` is its square root normalised by `c`: `c²s² = b − x`. Doing this
drops the plane model from total degree `8` to total degree `6`, kills
the auxiliary unknowns `b`, `c`, `x`, and leaves a curve which is a
CUBIC in `d` and a CUBIC in `s`.

THE ARITHMETIC, computed with Magma 2026-07-25 (untrusted searcher; every
number below is a fact ABOUT the curve, not a step of a Lean proof).
The smooth projective model is the hyperelliptic curve

    y² = x⁶ − 4x⁵ + 10x⁴ − 10x³ + 5x² − 2x + 1,   disc = 2¹⁵·3⁴

whose Jacobian has conductor `324 = 18²` — so this really is `J_1(18)`,
bad exactly at `2` and `3`. And:

* `J(ℚ)_tors ≅ ℤ/21` (the cuspidal group of `X_1(18)`);
* `RankBound(J) = 0`, i.e. **Mordell–Weil rank `0`**, so `J(ℚ) ≅ ℤ/21`
  is finite;
* a naive search to height `200` finds `6` rational points on it,
  `(1 : ±1 : 0)`, `(0, ±1)`, `(1, ±1)`;
* `#X(𝔽₅) = 6` (and `#X(𝔽₇) = 10`, `#X(𝔽₁₁) = 9`, `#X(𝔽₁₃) = 16`).

On the `(d, s)` model itself the only rational points found were the two
cusps `(0, −1)` and `(1, −1)`; the remaining four of the six sit over the
`(d, s)`-model's singular locus `(1 : −1 : 1)`, `(0 : 1 : 0)`,
`(1 : 0 : 0)` (Magma `SingularSubscheme`), i.e. over `d ∈ {0, 1, ∞}`.

**A COMPLETE PROOF IS THEREFORE IN REACH, and it is short.** Because
`J(ℚ)` is finite of order `21` and `5 ∤ 21`, reduction at the good odd
prime `5` is injective on `J(ℚ)`; composing with Abel–Jacobi
`X(ℚ) ↪ J(ℚ)` (any rational base point; `X` has genus `2 ≥ 1`, so two
rational points with the same reduction differ by a class killed in
`J(𝔽₅)`, hence are equal) gives `X(ℚ) ↪ X(𝔽₅)`. Since `#X(𝔽₅) = 6` and
`6` rational points are already exhibited, `X(ℚ)` is EXACTLY those `6`,
all cusps. No Chabauty, no Mordell–Weil sieve: only rank `0` plus one
point count over `𝔽₅`.

MISSING MACHINERY, in dependency order (none of it is in mathlib at this
pin `a3364fa`; `~/cs/FLT` has none of it either — its only Mazur-adjacent
file, `FLT/Assumptions/Mazur.lean`, states the result as an assumption):

1. hyperelliptic curves of genus `2` and their Jacobians as `Pic⁰`, with
   the Mumford representation and its group law;
2. the Abel–Jacobi embedding `X ↪ J` from a rational point;
3. good reduction `J(ℚ) → J(𝔽_p)` and its injectivity on prime-to-`p`
   torsion (mathlib has the elliptic-curve analogue nowhere either);
4. `rank J(ℚ) = 0` by `2`-descent: `J(ℚ)/2J(ℚ) ↪ Sel₂ ⊆ L*/(L*)²` for
   `L = ℚ[x]/(x⁶ − 4x⁵ + 10x⁴ − 10x³ + 5x² − 2x + 1)`. Mathlib DOES have
   the two inputs this needs — finiteness of the class group and
   Dirichlet's unit theorem — but no descent map and no Selmer group.

Item 4 is the only genuinely arithmetic one; 1–3 are geometry that has to
be written before it can be stated.

THREE SHORTCUTS, ALL CHECKED — two dead outright, one alive but strictly
more expensive than the rank-`0` argument above:

* *No elliptic-curve quotient to descend on OVER `ℚ`.* `S_2(Γ_0(18)) = 0`
  (`X_0(18)` has genus `0`), while all of the `2`-dimensional
  `S_2(Γ_1(18))` lies in the eigenspaces of a nebentypus of order `3`
  (PARI/GP `mfdim([18,2,0],1)` returns the single orbit with character
  `Mod(13,18)`, of order `3`). Confirmed geometrically 2026-07-25:
  `Aut_ℚ(X_1(18))` has order exactly `6` (Magma), namely
  `⟨ι⟩ × ⟨⟨5⟩⟩` with `ι` hyperelliptic and the diamond acting on the
  `d`-line by the order-`3` Möbius map `d ↦ 1/(1 − d)` (it cycles the
  cusps `0 → 1 → ∞ → 0` and preserves both `d³ − 6d² + 3d + 1` and
  `d² − d + 1`). The reduced group over `ℚ` is thus `ℤ/3`, containing no
  involution besides `ι`, so there is no elliptic quotient over `ℚ`.

  *But the Jacobian DOES split geometrically, and that is worth
  recording rather than glossing:* `Aut_ℚ̄` has order `12` (`D₁₂`), so
  there are three extra involutions and `Jac ~ E × E'` over `ℚ̄`.
  Diagonalising the diamond over `ℚ(ζ₃)` — send its fixed points
  `x² − x + 1 = 0` to `0, ∞` — puts the curve in the shape
  `Y² = 3(1 + ζ₃)·(U⁶ + 10ζ₃·U³ + ζ₃²)`, whose extra involutions are
  `U ↦ c/U` with `c³ = ζ₃²`. So they are defined over `ℚ(ζ₉)` and over
  no quadratic field (checked: `#Aut = 6` over each of `ℚ(√D)` for
  `D = −3, −1, ±2, ±3, ±6, 5, ±15`). Elliptic Chabauty is therefore
  available only over the cyclic sextic field `ℚ(ζ₉)`, where it needs
  `rank E(ℚ(ζ₉)) < 6` — HEAVIER machinery than the rank-`0` argument
  above, not lighter. Prefer the rank-`0` route.
* *No local obstruction can exist.* The cusps are rational points, so
  the curve has points everywhere locally; the content is that the
  rational points are ALL cuspidal, which no congruence argument can
  deliver.
* *The `X_0` / isogeny shortcut is unavailable* — `18` is a rational
  cyclic isogeny degree; see the parent docstring.

EVIDENCE THAT THE STATEMENT IS TRUE AS WRITTEN. Three independent
exhaustive PARI/GP searches, all empty of nondegenerate solutions:

* over this model, `73087` values `s = p/q` in lowest terms with
  `|p| ≤ 400`, `q ≤ 150`, solving the resulting CUBIC in `d` for rational
  roots — the only rational points found at all were the two cusps
  `(d, s) = (0, −1)` and `(1, −1)`;
* over the intermediate model in `z = s(d − 1)`, `43849` values with
  `|p| ≤ 300`, `q ≤ 120`, solving the resulting QUARTIC in `d` — empty;
* the complementary direction: `43847` nondegenerate `d = p/q` with
  `|p| ≤ 300`, `q ≤ 120`, solving the resulting CUBIC in `s` — empty.

The first two search over the SECOND coordinate and solve for `d`, so
they also cover rational points whose `d` has enormous height, which a
naive `d`-scan (the only search recorded before this cut) cannot see;
the third covers the reverse asymmetry. The family itself was
cross-checked independently:
`ellorder` confirms `(0,0)` has order exactly `9` on `[1−c, −b, −b, 0, 0]`
for `d = 2, …, 6`, and `elldisc` at `d = 2` gives `−124416`, matching
`delta_param`. Kenku–Ligozat–Kubert; subsumed in Mazur 1977, Thm 8. -/
theorem no_rational_point_on_X18 (d s : ℚ) (hd0 : d ≠ 0) (hd1 : d ≠ 1)
    (hcub : d ^ 3 - 6 * d ^ 2 + 3 * d + 1 ≠ 0)
    (hs : (2 * s + 1) * (d ^ 2 * (d - 1) * s ^ 2 - (d ^ 2 - d + 1)) = s ^ 2) :
    False :=
  sorry

/-- **The `2`-division cubic has no rational root along the level-`9`
family** (PROVEN 2026-07-25 modulo the descended curve
`no_rational_point_on_X18`; previously the bare `X_1(18)` sorry node).

The whole content of THIS declaration is the `2`-descent step, and it is
elementary. The `2`-division cubic is a difference of squares,

    4x³ + ((1−c)² − 4b)x² − 2b(1−c)x + b² = ((1−c)x − b)² − 4x²(b − x),

a `ring` identity; `x ≠ 0` because the constant term is `b² ≠ 0`; so
setting `s := ((1 − c)x − b)/(2xc)` — legitimate, `c ≠ 0` on the
nondegenerate locus — gives at once

    c²s² = b − x        (the square condition), and
    x·(1 − c − 2cs) = b (the linear relation defining `s`).

Eliminating `x` between them turns the cubic into
`(b − c²s²)(1 − c − 2cs) = b`, and with `b = ce` that factors as
`c²·[(2s + 1)(cs² − e) − s²] = 0`, so `(2s + 1)(cs² − e) = s²`: the
plane model of `X_1(18)` used by `no_rational_point_on_X18`.

Note that the passage is a genuine birational identification and not a
weakening — `x = b − c²s²` recovers `x` from `s` — so no content is lost
and no case is dropped: `c ≠ 0` and `x ≠ 0` are both consequences of the
hypotheses, not extra assumptions. -/
theorem no_rational_two_torsion_abscissa (d b c x : ℚ)
    (hc : c = d ^ 2 * (d - 1)) (hb : b = c * (d ^ 2 - d + 1))
    (hd0 : d ≠ 0) (hd1 : d ≠ 1) (hcub : d ^ 3 - 6 * d ^ 2 + 3 * d + 1 ≠ 0)
    (hx : 4 * x ^ 3 + ((1 - c) ^ 2 - 4 * b) * x ^ 2 - 2 * b * (1 - c) * x + b ^ 2 = 0) :
    False := by
  have he : d ^ 2 - d + 1 ≠ 0 := by
    intro h; nlinarith [sq_nonneg (2 * d - 1)]
  have hc0 : c ≠ 0 := by
    rw [hc]; exact mul_ne_zero (pow_ne_zero _ hd0) (sub_ne_zero.mpr hd1)
  have hb0 : b ≠ 0 := by rw [hb]; exact mul_ne_zero hc0 he
  -- the constant term of the cubic is `b²`, so the root is nonzero
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hb0 (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linear_combination hx))
  -- the descent coordinate: `2xc·s = (1 − c)x − b`
  obtain ⟨s, hs⟩ : ∃ s : ℚ, 2 * x * c * s = (1 - c) * x - b :=
    ⟨((1 - c) * x - b) / (2 * x * c), by field_simp⟩
  -- the square condition, from `((1−c)x − b)² = 4x²(b − x)`
  have hs2 : c ^ 2 * s ^ 2 = b - x := by
    have h4 : (4 : ℚ) * x ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hx0)
    have key : 4 * x ^ 2 * (c ^ 2 * s ^ 2 - (b - x)) = 0 := by
      linear_combination (2 * x * c * s + (1 - c) * x - b) * hs + hx
    have := (mul_eq_zero.mp key).resolve_left h4
    linarith
  -- the linear relation, and the elimination of `x` between the two
  have hxA : x * ((1 - c) - 2 * (c * s)) = b := by linear_combination -hs
  have hres : (b - c ^ 2 * s ^ 2) * ((1 - c) - 2 * (c * s)) - b = 0 := by
    linear_combination hxA - ((1 - c) - 2 * (c * s)) * hs2
  have hfin : c ^ 2 * ((2 * s + 1) * (c * s ^ 2 - (d ^ 2 - d + 1)) - s ^ 2) = 0 := by
    linear_combination hres + c * (1 + 2 * s) * hb
  refine no_rational_point_on_X18 d s hd0 hd1 hcub ?_
  have hcs := (mul_eq_zero.mp hfin).resolve_left (pow_ne_zero 2 hc0)
  rw [hc] at hcs
  linarith [hcs]

end MazurLevel18

/-- **Tate normal form at a rational point of order `9`** (PROVEN
2026-07-25; cut out of `not_order_two_and_order_nine_point` and then
closed): an
elliptic curve over `ℚ` carrying a rational point `Q` of order `9` is
`ℚ`-isomorphic to `y² + (1 − c)xy − by = x³ − bx²` by an isomorphism
taking `Q` to `(0,0)`, with `b ≠ 0` and nonzero discriminant.

This is the classical Tate normal form (Husemöller, *Elliptic Curves*,
ch. 4; Kubert 1976, §2), and it is ELEMENTARY — three changes of
variables, all defined over `ℚ`, none of them arithmetic:

1. `(u, r, s, t) = (1, X, s₀, Y)` moves `Q = (X, Y)` to `(0,0)`. The
   resulting `a₆` vanishes because `Q` is on the curve, and the
   resulting `a₃ = 2Y + a₁X + a₃` is nonzero because `Q` is not
   `2`-torsion.
2. `s₀ := (a₄ + 2Xa₂ − Ya₁ + 3X²)/(a₃ + Xa₁ + 2Y)` is the unique shear
   killing `a₄`, i.e. making the tangent at `Q` horizontal.
3. `(u, 0, 0, 0)` with `u := a₃'/a₂'` scales `a₂'` and `a₃'` to a
   common value `−b`. Here `a₂' ≠ 0` because `a₂' = 0` together with
   `a₄' = a₆' = 0` would force `x(2Q) = −a₂' = 0 = x(Q)`, hence
   `2Q = −Q` and `3Q = 0`, contradicting `addOrderOf Q = 9`.

Then `b := −a₂''` and `c := 1 − a₁''`. The point equivalence is the
composite of the two `Point.equivVariableChange` isomorphisms; each
sends `(0,0)` to `(r, t)`, so `(0,0) ↦ (0,0) ↦ (X, Y) = Q`.

The two changes of variables are carried out with
`WeierstrassCurve.variableChange_a₁ … a₆` (all `rfl` lemmas) and the
point equivalence with `Affine.Point.equivVariableChange`; the sibling
node `exists_normalForm_pointEquiv_of_rational_two_torsion` carries out
the same programme for the `2`-torsion normal form, over `ℚ̄` and with
Galois equivariance, which is why it is stated separately. -/
theorem WeierstrassCurve.exists_tateNormalForm_of_order_nine
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (Q : (E⁄ℚ).Point) (hQ : addOrderOf Q = 9) :
    ∃ (b c : ℚ) (_hb : b ≠ 0)
      (_hΔ : (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve ℚ).Δ ≠ 0)
      (h00 : (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve ℚ).toAffine.Nonsingular 0 0)
      (Ψ : (E⁄ℚ).Point ≃+ (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve ℚ).toAffine.Point),
      Ψ Q = Affine.Point.some 0 0 h00 := by
  haveI : (E⁄ℚ).IsElliptic := inferInstanceAs (E.map (algebraMap ℚ ℚ)).IsElliptic
  -- coordinates of `Q`
  have hQ0 : Q ≠ 0 := by rintro rfl; simp at hQ
  obtain ⟨X, Y, hns, hQxy⟩ :
      ∃ (X Y : ℚ) (h : (E⁄ℚ).toAffine.Nonsingular X Y), Q = Affine.Point.some X Y h := by
    rcases hcase : Q with _ | ⟨X, Y, h⟩
    · exact absurd hcase hQ0
    · exact ⟨X, Y, h, rfl⟩
  -- `Q` is not `2`-torsion, so `2Y + a₁X + a₃ ≠ 0`
  have hQ2 : Q + Q ≠ 0 := by
    intro h
    have hd : addOrderOf Q ∣ 2 := addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by rw [two_nsmul]; exact h)
    rw [hQ] at hd; norm_num at hd
  have hwne : Y ≠ (E⁄ℚ).toAffine.negY X Y := fun h =>
    hQ2 (by rw [hQxy]; exact Point.add_self_of_Y_eq h)
  have ha3ne : (E⁄ℚ).a₃ + X * (E⁄ℚ).a₁ + 2 * Y ≠ 0 := by
    intro h; exact hwne (by rw [Affine.negY]; linarith [h])
  -- the translating/shearing change of variables
  set s₀ : ℚ := ((E⁄ℚ).a₄ + 2 * X * (E⁄ℚ).a₂ - Y * (E⁄ℚ).a₁ + 3 * X ^ 2)
      / ((E⁄ℚ).a₃ + X * (E⁄ℚ).a₁ + 2 * Y) with hs₀
  set C₁ : VariableChange ℚ := ⟨1, X, s₀, Y⟩ with hC₁
  have hE1a₃ : (C₁ • (E⁄ℚ)).a₃ = (E⁄ℚ).a₃ + X * (E⁄ℚ).a₁ + 2 * Y := by
    rw [WeierstrassCurve.variableChange_a₃, hC₁]; simp
  have hE1a₄ : (C₁ • (E⁄ℚ)).a₄ = 0 := by
    rw [WeierstrassCurve.variableChange_a₄, hC₁]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    rw [hs₀]
    field_simp
    ring
  have hE1a₆ : (C₁ • (E⁄ℚ)).a₆ = 0 := by
    have heq := hns.1
    rw [Affine.equation_iff] at heq
    rw [WeierstrassCurve.variableChange_a₆, hC₁]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    linear_combination -heq
  -- `(0,0)` is a nonsingular point of the sheared curve, and it corresponds to `Q`
  have h00' : (C₁ • (E⁄ℚ)).toAffine.Nonsingular 0 0 :=
    Affine.nonsingular_zero.mpr ⟨hE1a₆, Or.inl (by rw [hE1a₃]; exact ha3ne)⟩
  have hmap : Point.equivVariableChange (E⁄ℚ) C₁ (Point.some 0 0 h00') = Q := by
    rw [Point.equivVariableChange_some, hQxy]
    exact Point.some_eq_some _ (by simp [hC₁]) (by simp [hC₁])
  -- `a₂ ≠ 0` after the shear, else `(0,0)` — hence `Q` — would have order `3`
  have ha2ne : (C₁ • (E⁄ℚ)).a₂ ≠ 0 := by
    intro hz
    have h3P : Point.some 0 0 h00' + Point.some 0 0 h00' + Point.some 0 0 h00' = 0 :=
      MazurLevel18.order_three_of_a₂_eq_zero hz hE1a₄ (by rw [hE1a₃]; exact ha3ne) h00'
    have hQ3 : Q + Q + Q = 0 := by
      have hc := congrArg (Point.equivVariableChange (E⁄ℚ) C₁) h3P
      rwa [map_add, map_add, map_zero, hmap] at hc
    have hd : addOrderOf Q ∣ 3 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by
        have e : (3 : ℕ) • Q = Q + Q + Q := by abel
        rw [e]; exact hQ3)
    rw [hQ] at hd; norm_num at hd
  -- the scaling that equalises `a₂` and `a₃`
  set u : ℚˣ := Units.mk0 ((C₁ • (E⁄ℚ)).a₃ / (C₁ • (E⁄ℚ)).a₂)
    (div_ne_zero (by rw [hE1a₃]; exact ha3ne) ha2ne)
  set C₂ : VariableChange ℚ := ⟨u, 0, 0, 0⟩ with hC₂
  have huv : (u : ℚ) = (C₁ • (E⁄ℚ)).a₃ / (C₁ • (E⁄ℚ)).a₂ := rfl
  have hune : (u : ℚ) ≠ 0 := u.ne_zero
  set b : ℚ := -(C₂ • (C₁ • (E⁄ℚ))).a₂ with hbdef
  set c : ℚ := 1 - (C₂ • (C₁ • (E⁄ℚ))).a₁ with hcdef
  have hA4 : (C₂ • (C₁ • (E⁄ℚ))).a₄ = 0 := by
    rw [WeierstrassCurve.variableChange_a₄, hC₂]; simp [hE1a₄]
  have hA6 : (C₂ • (C₁ • (E⁄ℚ))).a₆ = 0 := by
    rw [WeierstrassCurve.variableChange_a₆, hC₂]; simp [hE1a₆]
  have hA23 : (C₂ • (C₁ • (E⁄ℚ))).a₃ = (C₂ • (C₁ • (E⁄ℚ))).a₂ := by
    rw [WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₂, hC₂]
    simp only [Units.val_inv_eq_inv_val]
    field_simp [huv]
    rw [huv]; field_simp
    ring
  have hA2v : (C₂ • (C₁ • (E⁄ℚ))).a₂ = ((u : ℚ))⁻¹ ^ 2 * (C₁ • (E⁄ℚ)).a₂ := by
    rw [WeierstrassCurve.variableChange_a₂, hC₂]; simp
  have hA2ne : (C₂ • (C₁ • (E⁄ℚ))).a₂ ≠ 0 := by
    rw [hA2v]; exact mul_ne_zero (pow_ne_zero 2 (inv_ne_zero hune)) ha2ne
  have hbne : b ≠ 0 := by rw [hbdef, neg_ne_zero]; exact hA2ne
  have hEq : C₂ • (C₁ • (E⁄ℚ)) = (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve ℚ) := by
    ext <;> simp [hbdef, hcdef, hA4, hA6, hA23]
  have h00'' : (C₂ • (C₁ • (E⁄ℚ))).toAffine.Nonsingular 0 0 :=
    Affine.nonsingular_zero.mpr ⟨hA6, Or.inl (by rw [hA23]; exact hA2ne)⟩
  have hΔE : (E⁄ℚ).Δ ≠ 0 := (WeierstrassCurve.isUnit_Δ (W := (E⁄ℚ))).ne_zero
  have hΔ2 : (C₂ • (C₁ • (E⁄ℚ))).Δ ≠ 0 := by
    rw [WeierstrassCurve.variableChange_Δ, WeierstrassCurve.variableChange_Δ]
    exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero _))
      (mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) hΔE)
  refine ⟨b, c, hbne, hEq ▸ hΔ2, hEq ▸ h00'',
    (Point.equivVariableChange (E⁄ℚ) C₁).symm.trans
      ((Point.equivVariableChange (C₁ • (E⁄ℚ)) C₂).symm.trans (Point.equivOfEq hEq)), ?_⟩
  have e1 : (Point.equivVariableChange (E⁄ℚ) C₁).symm Q = Point.some 0 0 h00' := by
    rw [← hmap]; exact (Point.equivVariableChange (E⁄ℚ) C₁).symm_apply_apply _
  have e2 : (Point.equivVariableChange (C₁ • (E⁄ℚ)) C₂) (Point.some 0 0 h00'')
      = Point.some 0 0 h00' := by
    rw [Point.equivVariableChange_some]
    exact Point.some_eq_some _ (by simp [hC₂]) (by simp [hC₂])
  simp only [AddEquiv.trans_apply, e1, ← e2, AddEquiv.symm_apply_apply, Point.equivOfEq_some]

/-- **No rational point of order `2` together with a rational point of
order `9`** (PROVEN 2026-07-25; previously a bare sorry node): no
elliptic curve over `ℚ` carries both. The whole reduction is proven
here; its direct input `MazurLevel18.no_rational_two_torsion_abscissa`
is PROVEN too (2026-07-25), so the single surviving sorry beneath this
node is `MazurLevel18.no_rational_point_on_X18`, the explicit
`X_1(18)` Diophantine statement in its descended plane model — do NOT
dispatch at `no_rational_two_torsion_abscissa`. The hypotheses say
exactly that `E(ℚ) ⊇ ℤ/2 ⊕ ℤ/9 ≅ ℤ/18`, i.e. that `(E, P + Q)` is a
non-cuspidal rational point of `X_1(18)` — a curve of genus `2`
(recomputed 2026-07-25: `μ/12 = 9`, `16` cusps, so `g = 1 + 9 − 8 = 2`)
with no non-cuspidal rational point (Kenku–Ligozat–Kubert; subsumed in
Mazur 1977, Thm 8).

IRREDUCIBLE at this mathlib pin (audit 2026-07-25). Equivalent to
`no_torsion_order_18` below, but stated as the fibre product
`X_1(2) ×_{X_1(1)} X_1(9)` of two genus-`0` modular curves. Routes
checked and rejected:

* *The `X_0` / isogeny shortcut is NOT available here.* `18` is a
  rational cyclic isogeny degree: `[1,−1,1,−5,−7]` of conductor `126`
  has isogeny-degree set `{1, 2, 3, 6, 9, 18}` (PARI/GP `ellisomat`,
  witness recomputed 2026-07-25), so `X_0(18)` has non-cuspidal
  rational points.
* *Divisor reduction fails by design.* The proper divisors
  `1, 2, 3, 6, 9` all lie in Mazur's allowed set.
* *Reduction plus Hasse only bounds the conductor.* `18 ∣ #Ẽ(𝔽_p)` at
  every odd prime `p` of good reduction and `9 ∣ #Ẽ(𝔽_2)` at `p = 2`;
  since `p + 1 + 2√p < 18` for `p ≤ 7` and `#Ẽ(𝔽_2) ≤ 5 < 9`, bad
  reduction is forced at `2, 3, 5, 7` (`210 ∣ N_E`) and no further.

SUPERSEDED (2026-07-25) — the "IRREDUCIBLE at this mathlib pin" verdict
above was about the node as a whole, and it no longer applies to THIS
declaration: the level-`9` Tate normal form anticipated in the last
paragraph (`c = d²(d − 1)`, `b = c(d(d − 1) + 1)`, note
`d(d − 1) + 1 = d² − d + 1`) has been carried out, and the node is now
PROVEN from the two leaves stated just above. The irreducibility claim
survives only for `MazurLevel18.no_rational_point_on_X18`, where
it is restated with its evidence; the `X_0`, divisor-reduction and
Hasse-bound refutations recorded above are unaffected and still apply
to that leaf.

The assembly: transport `Q` to `(0,0)` of a Tate curve `E(b,c)`, read
off `9 • (0,0) = 0` to get `ψ₃(c) = 0` (`MazurLevel18.psi3_eq_zero`),
transport `P` too and read off its abscissa as a root of the
`2`-division cubic (`MazurLevel18.two_division_cubic`), pass to the
Kubert parameter `d` (`MazurLevel18.exists_param`), convert the
discriminant into the three nondegeneracy conditions
(`MazurLevel18.delta_param`), and apply the `X_1(18)` leaf. -/
theorem WeierstrassCurve.not_order_two_and_order_nine_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (P Q : (E⁄ℚ).Point)
    (hP : addOrderOf P = 2) (hQ : addOrderOf Q = 9) : False := by
  obtain ⟨b, c, hb, hΔ, h00, Ψ, hΨ⟩ := E.exists_tateNormalForm_of_order_nine Q hQ
  set W : WeierstrassCurve.Affine ℚ := (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve ℚ).toAffine
  have h1 : W.a₁ = 1 - c := rfl
  have h2 : W.a₂ = -b := rfl
  have h3 : W.a₃ = -b := rfl
  have h4 : W.a₄ = 0 := rfl
  have h6 : W.a₆ = 0 := rfl
  -- the order-`9` condition at `(0,0)`, i.e. `ψ₃(c) = 0`
  have hQ9 : (9 : ℕ) • Q = 0 := by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q
  have h9 : (9 : ℕ) • (Affine.Point.some 0 0 h00 : W.Point) = 0 := by
    rw [← hΨ, ← map_nsmul, hQ9, map_zero]
  have hpsi := MazurLevel18.psi3_eq_zero h1 h2 h3 h4 hb h00 h9
  -- the rational `2`-torsion point, transported and its abscissa extracted
  have hP0 : P ≠ 0 := by rintro rfl; simp at hP
  have hPP : P + P = 0 := by
    have h2P : (2 : ℕ) • P = 0 := by rw [← hP]; exact addOrderOf_nsmul_eq_zero P
    rwa [two_nsmul] at h2P
  have hΨP0 : Ψ P ≠ 0 := fun h => hP0 (Ψ.injective (h.trans (map_zero Ψ).symm))
  have hΨPP : Ψ P + Ψ P = 0 := by rw [← map_add, hPP, map_zero]
  obtain ⟨x, y, hns, hxy⟩ :
      ∃ (x y : ℚ) (hns : W.Nonsingular x y), Ψ P = Affine.Point.some x y hns := by
    rcases hcase : Ψ P with _ | ⟨x, y, hns⟩
    · exact absurd hcase hΨP0
    · exact ⟨x, y, hns, rfl⟩
  rw [hxy] at hΨPP
  have hy : y = W.negY x y := by
    by_contra hcon
    rw [Affine.Point.add_self_of_Y_ne hcon] at hΨPP
    exact Affine.Point.some_ne_zero _ hΨPP
  have hcubic := MazurLevel18.two_division_cubic (W := W) hns.1 hy
  rw [h1, h2, h3, h4, h6] at hcubic
  -- pass to the Kubert parameter and read the nondegeneracy off `Δ`
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hb (pow_eq_zero_iff (n := 3) (by norm_num) |>.mp (by linear_combination -hpsi))
  obtain ⟨d, hcd, hbd⟩ := MazurLevel18.exists_param hc0 hpsi
  rw [MazurLevel18.delta_param d hcd hbd] at hΔ
  have hd0 : d ≠ 0 := by rintro rfl; exact hΔ (by ring)
  have hd1 : d ≠ 1 := by rintro rfl; exact hΔ (by ring)
  have hcub : d ^ 3 - 6 * d ^ 2 + 3 * d + 1 ≠ 0 := fun h => hΔ (by rw [h]; ring)
  exact MazurLevel18.no_rational_two_torsion_abscissa d b c x hcd hbd hd0 hd1 hcub
    (by linear_combination hcubic)

/-- **No rational point of order `18`** (DERIVED 2026-07-25 from the
level-structure leaf `not_order_two_and_order_nine_point` by splitting
`ℤ/18` into its `2`- and `3`-primary parts): a point `Q` of order `18`
gives the order-`2` point `9 • Q` and the order-`9` point `2 • Q`.
`X_1(18)` has genus `2` and no non-cuspidal rational point
(Kenku–Ligozat–Kubert; subsumed in Mazur 1977, Thm 8). -/
theorem WeierstrassCurve.no_torsion_order_18 (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (Q : (E⁄ℚ).Point) : addOrderOf Q ≠ 18 := by
  intro hQ
  refine E.not_order_two_and_order_nine_point ((9 : ℕ) • Q) ((2 : ℕ) • Q) ?_ ?_
  · rw [addOrderOf_nsmul' Q (by decide), hQ]; decide
  · rw [addOrderOf_nsmul' Q (by decide), hQ]; decide

/-- **No rational point of order `20`** (PROVEN 2026-07-25 from the
`X_0` node `mem_cyclicIsogenyDegrees`): a rational point of order `20`
generates a rational — hence pointwise Galois-fixed, hence stable —
cyclic subgroup of order `20`, i.e. a rational cyclic `20`-isogeny; but
`20` is not a cyclic isogeny degree over `ℚ` (`X_0(20)` has genus `1`,
Mordell–Weil rank `0`, and its `6` rational points are exactly its `6`
cusps), so `20` is missing from Kenku's list.

The finer `X_1(20)` statement (genus `3`, no non-cuspidal rational
point) is NOT assumed anywhere: by the criterion in the section note
this level goes through `X_0`, so `mem_cyclicIsogenyDegrees` is the
single citation behind it. The exclusion recorded here earlier still
holds and is unaffected: this level is NOT reducible to
`not_two_torsion_and_five_point`, since a point of order `20` supplies
only ONE rational `2`-torsion point, not the full `(ℤ/2)²`. -/
theorem WeierstrassCurve.no_torsion_order_20 (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (Q : (E⁄ℚ).Point) : addOrderOf Q ≠ 20 := by
  intro hQ
  have h := E.mem_cyclicIsogenyDegrees_of_addOrderOf Q (by norm_num) hQ
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  omega

/-!
##### Level `21`: the `X_0(21) ∩ X_1(7)` cut (2026-07-25)

`no_torsion_order_21` used to be a bare genus-`5` citation (`X_1(21)` has
genus `5`; Chabauty on its Jacobian). It is now PROVEN from two strictly
shallower leaves whose images in the `j`-line are disjoint, plus an
arithmetic computation that is discharged in full here.

A rational point `Q` of order `21` supplies TWO independent pieces of level
structure, and it suffices to intersect the two loci they cut out on the
`j`-line — neither of which is `X_1(21)`:

* `⟨Q⟩` is a rational — indeed pointwise Galois-FIXED — cyclic subgroup of
  order `21`, i.e. a non-cuspidal rational point of `X_0(21)`. That curve
  has genus `1`: it is the elliptic curve `21a1 = [1,0,0,−4,−1]`, of
  Mordell–Weil rank `0` with `#X_0(21)(ℚ) = 8` (torsion `ℤ/4 × ℤ/2`), and
  `21` being squarefree with two prime factors it has `2² = 4` cusps. So
  there are exactly FOUR non-cuspidal rational points; that is
  `j_mem_of_cyclic_twentyOne_isogeny`.
* `3 • Q` is a rational point of order `7`, so `E` lies in the level-`7`
  Tate normal form family — `X_1(7)` has genus `0`, with explicit rational
  parameter `d`, `b = d³ − d²`, `c = d² − d`; that is
  `exists_levelSeven_jParam`.

**The two loci do not meet, and the reason is a single congruence** — which
is what makes the intersection a finite computation rather than another
Chabauty problem. Each of the four `X_0(21)` values has strictly positive
`5`-adic valuation and a denominator that is a power of `2`:

  `3375/2 = 5³·27/2`,   `−140625/8 = −5⁶·9/2³`,
  `−189613868625/128 = −5³·1516910949/2⁷`,
  `−1159088625/2097152 = −5³·9272709/2²¹`.

The level-`7` `j`-map never takes such a value. Writing the parameter in
lowest terms as `d = n/m`, the numerator of `j` is `c₄(n,m)³` for the
degree-`8` homogeneous form `c₄`, and `c₄` has NO zero on `ℙ¹(𝔽₅)` — a
`25`-case check discharged by `decide` in `MazurLevelSeven.cFourHom_mod_five`.
So `5` never divides the numerator of `j` for a curve with a rational
`7`-torsion point, while it divides all four of the values above.

Routes checked and REJECTED on the way, recorded so they are not retried:

* *The `X_0` shortcut alone is not enough.* `21` IS a rational cyclic
  isogeny degree, so `mem_cyclicIsogenyDegrees` yields no contradiction at
  all. The cut above uses `X_0(21)` for the `j`-VALUES, not for the degree,
  and that is exactly the extra strength it needs.
* *The level-`3` refinement FAILS.* Replacing the order-`7` point by the
  order-`3` point `7 • Q` gives a far cheaper genus-`0` family,
  `y² + a₁xy + a₃y = x³` with `j = t(t−24)³/(t−27)` and `t = a₁³/a₃`, of
  degree `4` instead of `24`. But every one of the four quartics
  `t(t−24)³ − j₀(t−27)` HAS a rational root — `t = 9`, `−27/2`, `−1125`,
  `3375/128` respectively — as it must, since two of the four curves
  literally have torsion `ℤ/3`. The `7`-torsion is the binding constraint;
  the `3`-torsion carries no information here.
* *Divisor reduction fails by design.* `21 = 3 · 7` and both `3` and `7`
  are permitted torsion orders, so neither the other levels nor
  `no_prime_torsion_ge_eleven` applies.
* *Reduction plus Hasse only bounds the conductor.* `21` is odd, so the
  point injects into `Ẽ(𝔽_p)` at every prime `p` of good reduction, `p = 2`
  included; `21 ≤ ⌊p + 1 + 2√p⌋` forces bad reduction exactly at
  `2, 3, 5, 7, 11`, while at `p = 13` already `#Ẽ(𝔽_13) = 21` is
  Hasse-admissible (`a₁₃ = −7`). A lower bound on `N_E` is never a
  contradiction.

The four `j`-invariants and the isogeny structure were FOUND with PARI/GP
(`ellisomat` on `[1,−1,0,3,−1]` of conductor `162`, whose class is exactly
four curves with degree matrix `[1,3,7,21; 3,1,21,7; 7,21,1,3; 21,7,3,1]`,
so the four curves carry one rational cyclic `21`-subgroup each) — an
untrusted searcher, never a proof: the mod-`5` fact that the argument
actually rests on is re-verified inside Lean by `decide` below, and the
`5`-adic valuations by `norm_num`.
-/

namespace MazurLevelSeven

/-- **`c₄` of the level-`7` Tate normal form** (PROVEN correct against
PARI/GP, 2026-07-25): for `E_d : y² + (1−c)xy − by = x³ − bx²` with
`b = d³ − d²` and `c = d² − d` — the universal elliptic curve with a point
of order `7` at `(0,0)` — this polynomial is exactly `E_d.c₄`. -/
def cFourPoly (d : ℚ) : ℚ :=
  d ^ 8 - 12 * d ^ 7 + 42 * d ^ 6 - 56 * d ^ 5 + 35 * d ^ 4 - 14 * d ^ 2 + 4 * d + 1

/-- **The discriminant of the level-`7` Tate normal form** (PROVEN correct
against PARI/GP, 2026-07-25): `Δ(E_d) = d⁷(d−1)⁷(d³ − 8d² + 5d + 1)`. Its
three factors are the three ways `E_d` degenerates, and `j = c₄³/Δ` is the
degree-`24` map `X_1(7) → X(1)`, matching `[PSL₂(ℤ) : Γ̄₁(7)] = 24`. -/
def discPoly (d : ℚ) : ℚ :=
  d ^ 7 * (d - 1) ^ 7 * (d ^ 3 - 8 * d ^ 2 + 5 * d + 1)

/-- Degree-`8` homogenization of `cFourPoly`: `cFourHom n m = m⁸ · c₄(n/m)`. -/
def cFourHom (n m : ℤ) : ℤ :=
  n ^ 8 - 12 * n ^ 7 * m + 42 * n ^ 6 * m ^ 2 - 56 * n ^ 5 * m ^ 3 + 35 * n ^ 4 * m ^ 4
    - 14 * n ^ 2 * m ^ 6 + 4 * n * m ^ 7 + m ^ 8

/-- Degree-`17` homogenization of `discPoly`: `discHom n m = m¹⁷ · Δ(n/m)`. -/
def discHom (n m : ℤ) : ℤ :=
  n ^ 7 * (n - m) ^ 7 * (n ^ 3 - 8 * n ^ 2 * m + 5 * n * m ^ 2 + m ^ 3)

/-- **`c₄` has no zero on `ℙ¹(𝔽₅)`** (PROVEN by exhaustive `decide` over the
`25` pairs): this single congruence is the whole reason the `X_0(21)` and
`X_1(7)` loci are disjoint. Note it genuinely needs the projective form —
`c₄(0,0) = 0`, so coprimality of `(n, m)` is doing work. -/
lemma cFourHom_mod_five : ∀ x y : ZMod 5, (x ≠ 0 ∨ y ≠ 0) →
    x ^ 8 - 12 * x ^ 7 * y + 42 * x ^ 6 * y ^ 2 - 56 * x ^ 5 * y ^ 3 + 35 * x ^ 4 * y ^ 4
      - 14 * x ^ 2 * y ^ 6 + 4 * x * y ^ 7 + y ^ 8 ≠ 0 := by decide

/-- Homogenization identity for `c₄` (PROVEN — pure field algebra). -/
lemma cFourPoly_hom (n m : ℤ) (hm : (m : ℚ) ≠ 0) :
    (m : ℚ) ^ 8 * cFourPoly ((n : ℚ) / (m : ℚ)) = (cFourHom n m : ℚ) := by
  unfold cFourPoly cFourHom
  push_cast
  field_simp

/-- Homogenization identity for `Δ` (PROVEN — pure field algebra). -/
lemma discPoly_hom (n m : ℤ) (hm : (m : ℚ) ≠ 0) :
    (m : ℚ) ^ 17 * discPoly ((n : ℚ) / (m : ℚ)) = (discHom n m : ℚ) := by
  unfold discPoly discHom
  push_cast
  field_simp

/-- **`5` never divides `c₄(n, m)` for coprime `(n, m)`** (PROVEN from the
`decide` check by reduction mod `5`). -/
lemma five_not_dvd_cFourHom {n m : ℤ} (h : ¬((n : ZMod 5) = 0 ∧ (m : ZMod 5) = 0)) :
    ¬ (5 : ℤ) ∣ cFourHom n m := by
  intro hdvd
  have hz : ((cFourHom n m : ℤ) : ZMod 5) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mpr (by exact_mod_cast hdvd)
  have hx : ((n : ZMod 5) ≠ 0 ∨ (m : ZMod 5) ≠ 0) := by
    rcases eq_or_ne (n : ZMod 5) 0 with h1 | h1
    · exact Or.inr fun h2 => h ⟨h1, h2⟩
    · exact Or.inl h1
  refine cFourHom_mod_five _ _ hx ?_
  rw [← hz]
  unfold cFourHom
  push_cast
  ring

/-- **The level-`7` `j`-map never takes a value whose numerator is divisible
by `5` and whose denominator is a power of `2`** (PROVEN 2026-07-25 — this is
the arithmetic heart of `no_torsion_order_21`).

Given `j₀ · 2ᵉ = u` with `5 ∣ u`, no rational `d` satisfies
`j₀ · Δ(d) = c₄(d)³`. Writing `d = n/m` in lowest terms and clearing
denominators turns that equation into the integer identity
`u · m⁷ · Δ(n,m) = 2ᵉ · c₄(n,m)³`; since `5 ∣ u` and `5 ∤ 2ᵉ`, this forces
`5 ∣ c₄(n,m)`, which `five_not_dvd_cFourHom` refutes.

Note the hypothesis `Δ(d) ≠ 0` is NOT needed: if `Δ(d) = 0` the equation
forces `c₄(d) = 0` and the same contradiction applies. -/
theorem j_ne_of_five_dvd {u : ℤ} {e : ℕ} {j₀ : ℚ} (hu : (5 : ℤ) ∣ u)
    (hj : j₀ * 2 ^ e = (u : ℚ)) (d : ℚ) :
    j₀ * discPoly d ≠ (cFourPoly d) ^ 3 := by
  intro h
  set n : ℤ := d.num with hn
  set m : ℤ := (d.den : ℤ) with hm
  have hdpos : (0 : ℚ) < (d.den : ℚ) := by exact_mod_cast d.pos
  have hm0 : (m : ℚ) ≠ 0 := by rw [hm]; push_cast; exact ne_of_gt hdpos
  have hd : d = (n : ℚ) / (m : ℚ) := by
    rw [hn, hm]; push_cast; exact (Rat.num_div_den d).symm
  have h1 : (m : ℚ) ^ 8 * cFourPoly d = (cFourHom n m : ℚ) := by
    conv_lhs => rw [hd]
    exact cFourPoly_hom n m hm0
  have h2 : (m : ℚ) ^ 17 * discPoly d = (discHom n m : ℚ) := by
    conv_lhs => rw [hd]
    exact discPoly_hom n m hm0
  have h' : (u : ℚ) * discPoly d = 2 ^ e * (cFourPoly d) ^ 3 := by
    rw [← hj]; linear_combination (2 : ℚ) ^ e * h
  have key : (u : ℚ) * (m : ℚ) ^ 7 * (discHom n m : ℚ) = 2 ^ e * ((cFourHom n m : ℚ)) ^ 3 := by
    rw [← h1, ← h2]; linear_combination (m : ℚ) ^ 24 * h'
  have keyZ : u * m ^ 7 * discHom n m = 2 ^ e * (cFourHom n m) ^ 3 := by exact_mod_cast key
  have hp5 : Prime (5 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by decide)
  have h5 : (5 : ℤ) ∣ 2 ^ e * (cFourHom n m) ^ 3 := by
    rw [← keyZ]; exact Dvd.dvd.mul_right (Dvd.dvd.mul_right hu _) _
  have hcH : (5 : ℤ) ∣ cFourHom n m := by
    rcases (hp5.dvd_mul).mp h5 with hc | hc
    · exact absurd (hp5.dvd_of_dvd_pow hc) (by norm_num)
    · exact hp5.dvd_of_dvd_pow hc
  refine five_not_dvd_cFourHom ?_ hcH
  rintro ⟨hn5, hm5⟩
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hn5 hm5
  have hg := Int.dvd_gcd hn5 hm5
  have hcop : Int.gcd n m = 1 := by
    rw [hn, hm]
    simpa [Int.gcd, Nat.Coprime] using d.reduced
  rw [hcop] at hg
  norm_num at hg

end MazurLevelSeven

/-- **The `j`-invariants of the four curves with a rational cyclic
`21`-isogeny** (sorry node — the `X_0(21)` input, and the ONLY modular
citation left at this level): if the cyclic subgroup `⟨g⟩` generated by a
geometric point `g` of an elliptic curve `E/ℚ` has exact order `21` and is
stable under `Gal(ℚ̄/ℚ)`, then

  `j(E) ∈ {3375/2, −140625/8, −189613868625/128, −1159088625/2097152}`.

This is the determination of the non-cuspidal rational points of `X_0(21)`.
That modular curve has genus `1`; concretely it is the elliptic curve
`21a1 = [1,0,0,−4,−1]`, whose Mordell–Weil group is `ℤ/4 × ℤ/2` — rank `0`,
`8` rational points. Level `21` is squarefree with two prime factors, so
`X_0(21)` has `2² = 4` cusps, leaving exactly `4` non-cuspidal rational
points; they are the four curves of the conductor-`162` isogeny class, whose
`j`-invariants are the values above.

STRICTLY WEAKER than the genus-`5` `X_1(21)` citation this node replaced:
`X_0(21)` is a rank-`0` ELLIPTIC curve, so its rational points are a
Mordell–Weil computation, not a Chabauty argument on a genus-`5` Jacobian.
It is also a refinement of the same Kenku input that
`composite_mem_cyclicIsogenyDegrees` already carries — that node records
that `21` occurs as a cyclic isogeny degree, this one records WHICH curves
realise it — so the tree gains no new source, only a sharper reading of one
it already cites.

IRREDUCIBLE at this mathlib pin, for the same reason as the neighbouring
`X_0` nodes: no modular curve, no Jacobian and no Mordell–Weil machinery
exists in this development. -/
theorem WeierstrassCurve.j_mem_of_cyclic_twentyOne_isogeny (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (g : (E⁄(AlgebraicClosure ℚ)).Point) (hg : addOrderOf g = 21)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    E.j ∈ ({3375 / 2, -140625 / 8, -189613868625 / 128,
      -1159088625 / 2097152} : Finset ℚ) :=
  sorry

/-- **A rational point of order `21` pins down `j`** (PROVEN 2026-07-25 — the
same base-change bookkeeping as `mem_cyclicIsogenyDegrees_of_addOrderOf`,
feeding the `X_0(21)` node): a rational point `Q` of exact order `21`
generates a cyclic subgroup of order `21` in `E(ℚ̄)` all of whose elements
are base changes of rational points, hence pointwise Galois-FIXED and in
particular Galois-stable. -/
lemma WeierstrassCurve.j_mem_of_addOrderOf_twentyOne
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (Q : (E⁄ℚ).Point)
    (hQ : addOrderOf Q = 21) :
    E.j ∈ ({3375 / 2, -140625 / 8, -189613868625 / 128,
      -1159088625 / 2097152} : Finset ℚ) := by
  set g : (E⁄(AlgebraicClosure ℚ)).Point :=
    Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) Q with hgdef
  have hgfix : ∀ σ : Field.absoluteGaloisGroup ℚ,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom g = g := fun σ =>
    Affine.Point.map_baseChange
      (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom Q
  have hgord : addOrderOf g = 21 := by
    rw [← hQ, hgdef]
    exact addOrderOf_injective _
      (Affine.Point.map_injective (f := Algebra.ofId ℚ (AlgebraicClosure ℚ))) Q
  refine E.j_mem_of_cyclic_twentyOne_isogeny g hgord ?_
  intro σ x hx
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  rw [map_zsmul, hgfix σ]
  exact AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples g) k

/-- **The level-`7` Tate normal form, in its `j`-invariant shadow** (sorry
node — the `X_1(7)` input, a GENUS-`0` statement): if `E/ℚ` carries a
rational point `P` of order `7`, then there is a rational parameter `d` with
`Δ(d) ≠ 0` and

  `j(E) · Δ(d) = c₄(d)³`,

for the level-`7` polynomials of `MazurLevelSeven` above.

This is the classical Tate normal form at level `7` (Kubert, *Universal
bounds on the torsion of elliptic curves*, 1976, Table 3). The full
statement is the ℚ-ISOMORPHISM `E ≅ E_d` with

  `E_d : y² + (1 − c)xy − by = x³ − bx²`,  `b = d³ − d²`, `c = d² − d`,

carrying `P` to `(0,0)`; asserted here is only its `j`-invariant shadow,
which is what this level consumes and is invariant under the quadratic
twisting that the `j`-invariant alone cannot see.

ELEMENTARY, unlike its `X_0(21)` sibling: `X_1(7)` has genus `0` and the
parameter `d` is a rational coordinate on it, so no Mordell–Weil or Chabauty
input is involved. Proving it needs (i) the normalisation moving `P` to
`(0,0)` with `a₄ = a₆ = 0` and then scaling the tangent so that `a₂ = a₃`,
which is the general Tate normal form for a point of order `≥ 4`, and
(ii) the level-`7` condition `7 • P = 0`, which is what cuts `b, c` down to
the one-parameter family above. Both are explicit polynomial algebra; the
first is the same construction as
`exists_normalForm_pointEquiv_of_rational_two_torsion` further down this
file, one order up.

Numerically checked with PARI/GP (2026-07-25; untrusted searcher, never a
proof): for `d = 2, …, 7` the curve `E_d` has rational torsion of order
exactly `7`, and its `c₄`, `Δ` and `j` agree on the nose with `cFourPoly`,
`discPoly` and `c₄³/Δ`. Conversely `26b1 = [1,−1,1,−3,3]`, of torsion
`ℤ/7`, is hit at `d = 2, −1, 1/2`. -/
theorem WeierstrassCurve.exists_levelSeven_jParam (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (P : (E⁄ℚ).Point) (hP : addOrderOf P = 7) :
    ∃ d : ℚ, MazurLevelSeven.discPoly d ≠ 0 ∧
      E.j * MazurLevelSeven.discPoly d = (MazurLevelSeven.cFourPoly d) ^ 3 :=
  sorry

/-- **No rational point of order `21`** (PROVEN 2026-07-25 from the
`X_0(21)` node `j_mem_of_cyclic_twentyOne_isogeny`, the genus-`0` `X_1(7)`
node `exists_levelSeven_jParam`, and the mod-`5` computation
`MazurLevelSeven.j_ne_of_five_dvd`): a point `Q` of order `21` gives at once
a Galois-stable cyclic subgroup `⟨Q⟩` of order `21`, forcing `j(E)` into the
four-element `X_0(21)` list, and a rational point `3 • Q` of order `7`,
forcing `j(E)` into the image of the level-`7` `j`-map. Those two loci are
disjoint because every value in the list has `5` dividing its numerator and
a power of `2` as its denominator, while the level-`7` `j`-map never does.
See the section note above for the full account, including the routes that
fail. -/
theorem WeierstrassCurve.no_torsion_order_21 (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (Q : (E⁄ℚ).Point) : addOrderOf Q ≠ 21 := by
  intro hQ
  have h7 : addOrderOf ((3 : ℕ) • Q) = 7 := by
    rw [addOrderOf_nsmul' Q (by decide), hQ]; decide
  obtain ⟨d, -, hd⟩ := E.exists_levelSeven_jParam ((3 : ℕ) • Q) h7
  have hj := E.j_mem_of_addOrderOf_twentyOne Q hQ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with h | h | h | h
  · exact MazurLevelSeven.j_ne_of_five_dvd (u := 3375) (e := 1) (j₀ := E.j)
      (by norm_num) (by rw [h]; norm_num) d hd
  · exact MazurLevelSeven.j_ne_of_five_dvd (u := -140625) (e := 3) (j₀ := E.j)
      (by norm_num) (by rw [h]; norm_num) d hd
  · exact MazurLevelSeven.j_ne_of_five_dvd (u := -189613868625) (e := 7) (j₀ := E.j)
      (by norm_num) (by rw [h]; norm_num) d hd
  · exact MazurLevelSeven.j_ne_of_five_dvd (u := -1159088625) (e := 21) (j₀ := E.j)
      (by norm_num) (by rw [h]; norm_num) d hd

/-- **No rational point of order `24`** (PROVEN 2026-07-25 from the
`X_0` node `mem_cyclicIsogenyDegrees`): a rational point of order `24`
generates a rational, hence Galois-stable, cyclic subgroup of order
`24`, i.e. a rational cyclic `24`-isogeny; but `24` is not a cyclic
isogeny degree over `ℚ` (`X_0(24)` has genus `1`, Mordell–Weil rank
`0`, and its `8` rational points are exactly its `8` cusps), so `24` is
missing from Kenku's list.

The finer `X_1(24)` statement (genus `5`, no non-cuspidal rational
point) is NOT assumed anywhere: by the criterion in the section note
this level goes through `X_0`, so `mem_cyclicIsogenyDegrees` is the
single citation behind it. Note also that this level is not reducible
to `not_two_four_torsion_and_three_point`: a point of order `24` gives
a cyclic `ℤ/8`, never the `ℤ/2 × ℤ/4` that node needs. -/
theorem WeierstrassCurve.no_torsion_order_24 (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (Q : (E⁄ℚ).Point) : addOrderOf Q ≠ 24 := by
  intro hQ
  have h := E.mem_cyclicIsogenyDegrees_of_addOrderOf Q (by norm_num) hQ
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  omega

/-! ### The plane model of `X_1(N)` in Tate coordinates, PROVEN

`tateNormalForm b c` carries the origin `(0, 0)`, and "the origin has
order `N`" is a POLYNOMIAL condition on `(b, c)` — that is exactly what
makes the `(b, c)`-plane the affine model of `X_1(N)`. This section
proves the dictionary and evaluates it, so that the levels below become
concrete Diophantine statements about explicit plane curves rather than
statements about torsion.

The dictionary is `TorsionCard.smul_some_eq_zero_iff` (PROVEN, the
division-polynomial torsion dictionary `n • P = 0 ↔ ΨSqₙ(x_P) = 0`),
specialised to `x_P = 0`. Its right-hand side is a polynomial in `b, c`
because the whole `normEDS` recursion of mathlib's `preΨ'` is closed
under evaluation at a FIXED `x`: every term of `preΨ'_even` and
`preΨ'_odd` is evaluated at the same point. So the values
`wₙ := preΨ'ₙ(0)` satisfy a numerical recursion started from

  `Ψ₂Sq(0) = b₆ = b²`,  `Ψ₃(0) = b₈ = −b³`,
  `preΨ₄(0) = b₄b₈ − b₆² = −b⁴c`,

and each `wₙ` factors as `b^{kₙ} · Fₙ(b, c)` with `Fₙ` the level-`n`
plane curve. Since `b ≠ 0` on the whole family (`b = 0` makes the origin
singular), `wₙ = 0` is equivalent to `Fₙ(b, c) = 0`. Only the `wₙ` that
the levels below actually consume are recorded — `n = 5, 6, 7, 8, 11,
13`; the recursion produces any other in the same two lines.

The `Fₙ` were computed independently in PARI/GP (untrusted searcher,
never a proof — every value below is re-derived inside Lean from the
recursion, so a wrong guess is a compile error, not a false leaf) and
checked over `𝔽₂₃, 𝔽₆₇` for `N = 11` and `𝔽₅₃, 𝔽₇₉` for `N = 13`: at
every `(b, c)` where the origin of `tateNormalForm b c` has order `N`,
`F_N(b, c) = 0`, with no exceptions. A search over all `b, c` of height
`≤ 40` with denominator `≤ 12` found NO rational zero of `F₁₁` or `F₁₃`
with `b ≠ 0`, consistent with the two leaves below. -/

namespace MazurX1Plane

/-- **The torsion dictionary over `ℚ` itself**: base-changing a curve
over `ℚ` along `ℚ → ℚ` is the identity (`rfl`), so
`TorsionCard.smul_some_eq_zero_iff` applies verbatim to a point of the
curve itself. -/
theorem zsmul_eq_zero_iff (W : WeierstrassCurve ℚ) [W.IsElliptic] {x y : ℚ}
    (h : W.toAffine.Nonsingular x y) {n : ℤ} (hn : n ≠ 0) :
    n • (Affine.Point.some x y h) = 0 ↔ (W.ΨSq n).eval x = 0 :=
  TorsionCard.smul_some_eq_zero_iff W hn h

/-- **`b ≠ 0` on the whole Tate family** (PROVEN): `a₄ = a₆ = 0` and
`a₃ = −b`, so `Affine.nonsingular_zero` forces `−b ≠ 0`. -/
theorem b_ne_zero {b c : ℚ}
    (h00 : (WeierstrassCurve.tateNormalForm b c).toAffine.Nonsingular 0 0) : b ≠ 0 := by
  rw [WeierstrassCurve.tateNormalForm, Affine.nonsingular_zero] at h00
  rcases h00.2 with h | h
  · simpa using h
  · simp at h

/-- `Ψ₂Sq(0) = b₆ = b²`. -/
theorem eval_Ψ₂Sq (b c : ℚ) :
    ((WeierstrassCurve.tateNormalForm b c).Ψ₂Sq).eval 0 = b ^ 2 := by
  simp [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.tateNormalForm, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆]

/-- `Ψ₃(0) = b₈ = −b³`. -/
theorem eval_Ψ₃ (b c : ℚ) :
    ((WeierstrassCurve.tateNormalForm b c).Ψ₃).eval 0 = -b ^ 3 := by
  simp [WeierstrassCurve.Ψ₃, WeierstrassCurve.tateNormalForm, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- `preΨ₄(0) = b₄b₈ − b₆² = −b⁴c`. -/
theorem eval_preΨ₄ (b c : ℚ) :
    ((WeierstrassCurve.tateNormalForm b c).preΨ₄).eval 0 = -b ^ 4 * c := by
  simp [WeierstrassCurve.preΨ₄, WeierstrassCurve.tateNormalForm, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- The even `normEDS` recursion, evaluated at a fixed point. -/
theorem eval_preΨ'_even (W : WeierstrassCurve ℚ) (x : ℚ) (m : ℕ) :
    (W.preΨ' (2 * (m + 3))).eval x =
      (W.preΨ' (m + 2)).eval x ^ 2 * (W.preΨ' (m + 3)).eval x * (W.preΨ' (m + 5)).eval x -
        (W.preΨ' (m + 1)).eval x * (W.preΨ' (m + 3)).eval x * (W.preΨ' (m + 4)).eval x ^ 2 := by
  rw [W.preΨ'_even m]; simp

/-- The odd `normEDS` recursion, evaluated at a fixed point. -/
theorem eval_preΨ'_odd (W : WeierstrassCurve ℚ) (x : ℚ) (m : ℕ) :
    (W.preΨ' (2 * (m + 2) + 1)).eval x =
      (W.preΨ' (m + 4)).eval x * (W.preΨ' (m + 2)).eval x ^ 3 *
          (if Even m then (W.Ψ₂Sq.eval x) ^ 2 else 1) -
        (W.preΨ' (m + 1)).eval x * (W.preΨ' (m + 3)).eval x ^ 3 *
          (if Even m then 1 else (W.Ψ₂Sq.eval x) ^ 2) := by
  rw [W.preΨ'_odd m]; split <;> simp

/-- At an ODD index `ΨSqₙ = preΨ'ₙ²`, with no `Ψ₂Sq` factor. -/
theorem eval_ΨSq_odd (W : WeierstrassCurve ℚ) (x : ℚ) (n : ℕ) (hn : ¬ Even n) :
    (W.ΨSq (n : ℤ)).eval x = (W.preΨ' n).eval x ^ 2 := by
  rw [WeierstrassCurve.ΨSq_ofNat]; simp [hn]

/-- A vanishing `preΨ'ₙ` value forces a vanishing `ΨSqₙ` value, at
either parity. -/
theorem eval_ΨSq_of_preΨ' (W : WeierstrassCurve ℚ) (x : ℚ) (n : ℕ)
    (h : (W.preΨ' n).eval x = 0) : (W.ΨSq (n : ℤ)).eval x = 0 := by
  rw [WeierstrassCurve.ΨSq_ofNat]; split <;> simp [h]

/-! #### The level values `wₙ = preΨ'ₙ(0)` on `tateNormalForm b c` -/

/-- `w₅ = b⁸(b − c)`: the origin has order `5` exactly on the line
`b = c`, the classical genus-`0` model of `X_1(5)`. -/
theorem eval_five (b c : ℚ) :
    ((WeierstrassCurve.tateNormalForm b c).preΨ' 5).eval 0 = b ^ 8 * (b - c) := by
  have h := eval_preΨ'_odd (WeierstrassCurve.tateNormalForm b c) 0 0
  norm_num [Nat.even_iff, eval_Ψ₂Sq, eval_Ψ₃, eval_preΨ₄] at h
  rw [h]; ring

/-- `w₆ = b¹¹(−b + c² + c)`, the genus-`0` model of `X_1(6)`. -/
theorem eval_six (b c : ℚ) :
    ((WeierstrassCurve.tateNormalForm b c).preΨ' 6).eval 0 =
      b ^ 11 * (-b + c ^ 2 + c) := by
  have h := eval_preΨ'_even (WeierstrassCurve.tateNormalForm b c) 0 0
  norm_num [Nat.even_iff, eval_Ψ₃, eval_preΨ₄, eval_five] at h
  rw [h]; ring

/-- `w₇ = b¹⁶(−b² + cb + c³)`, the genus-`0` model of `X_1(7)` — the
same curve as `MazurLevelSeven`'s parametrisation `b = d³ − d²`,
`c = d² − d`, in implicit form. -/
theorem eval_seven (b c : ℚ) :
    ((WeierstrassCurve.tateNormalForm b c).preΨ' 7).eval 0 =
      b ^ 16 * (-b ^ 2 + c * b + c ^ 3) := by
  have h := eval_preΨ'_odd (WeierstrassCurve.tateNormalForm b c) 0 1
  norm_num [Nat.even_iff, eval_Ψ₂Sq, eval_Ψ₃, eval_preΨ₄, eval_five] at h
  rw [h]; ring

/-- `w₈ = b²⁰(2cb² − (c³ + 3c²)b + c³)`. -/
theorem eval_eight (b c : ℚ) :
    ((WeierstrassCurve.tateNormalForm b c).preΨ' 8).eval 0 =
      b ^ 20 * (2 * c * b ^ 2 + (-c ^ 3 - 3 * c ^ 2) * b + c ^ 3) := by
  have h := eval_preΨ'_even (WeierstrassCurve.tateNormalForm b c) 0 1
  norm_num [Nat.even_iff, eval_Ψ₃, eval_preΨ₄, eval_five, eval_six] at h
  rw [h]; ring

/-- **`w₁₁ = b⁴⁰F₁₁`, the plane model of `X_1(11)`.** -/
theorem eval_eleven (b c : ℚ) :
    ((WeierstrassCurve.tateNormalForm b c).preΨ' 11).eval 0 =
      b ^ 40 * (-b ^ 5 + 3 * c * b ^ 4 + (4 * c ^ 3 - 3 * c ^ 2) * b ^ 3
        + (-3 * c ^ 5 - 9 * c ^ 4 + c ^ 3) * b ^ 2
        + (c ^ 7 + 3 * c ^ 6 + 6 * c ^ 5) * b - c ^ 6) := by
  have h := eval_preΨ'_odd (WeierstrassCurve.tateNormalForm b c) 0 3
  norm_num [Nat.even_iff, eval_Ψ₂Sq, eval_preΨ₄, eval_five, eval_six, eval_seven] at h
  rw [h]; ring

/-- **`w₁₃ = b⁵⁶F₁₃`, the plane model of `X_1(13)`.** -/
theorem eval_thirteen (b c : ℚ) :
    ((WeierstrassCurve.tateNormalForm b c).preΨ' 13).eval 0 =
      b ^ 56 * (b ^ 7 - 6 * c * b ^ 6 + (4 * c ^ 3 + 15 * c ^ 2) * b ^ 5
        + (-9 * c ^ 5 - 15 * c ^ 4 - 20 * c ^ 3) * b ^ 4
        + (5 * c ^ 7 + 24 * c ^ 6 + 21 * c ^ 5 + 15 * c ^ 4) * b ^ 3
        + (-c ^ 9 - 6 * c ^ 8 - 21 * c ^ 7 - 13 * c ^ 6 - 6 * c ^ 5) * b ^ 2
        + (6 * c ^ 8 + 3 * c ^ 7 + c ^ 6) * b + c ^ 10) := by
  have h := eval_preΨ'_odd (WeierstrassCurve.tateNormalForm b c) 0 4
  norm_num [Nat.even_iff, eval_Ψ₂Sq, eval_five, eval_six, eval_seven, eval_eight] at h
  rw [h]; ring

end MazurX1Plane

/-- **`X_1(11)` has no non-cuspidal rational point, as a plane quintic**
(sorry node — level `11` of the seven-level node below, in the explicit
`(b, c)`-coordinates).

The polynomial is `F₁₁`, the cofactor of `b⁴⁰` in
`MazurX1Plane.eval_eleven`; by that PROVEN lemma and the PROVEN torsion
dictionary, `F₁₁(b, c) = 0` with `b ≠ 0` says exactly that the origin of
`tateNormalForm b c` has order `11`. So this node is the plane model of
`X_1(11)` and nothing more: it carries the same content as the old
`tateNormalForm_origin_order_ne_11`, with the modular curve replaced by
the explicit affine quintic that IS its `(b, c)`-model.

`X_1(11)` has genus `1`; it is the elliptic curve `11a3`,
`y² + y = x³ − x²`, with `X_1(11)(ℚ) ≅ ℤ/5` generated by a cusp, so all
five rational points are cusps and none is in the `b ≠ 0` chart.
Billing–Mahler (J. London Math. Soc. 15, 1940); subsumed in Mazur 1977,
Thm 7. A rank-`0` Mordell–Weil computation is what is missing; the
`X_0` shortcut is NOT available, since `11` is in Kenku's list and
`X_0(11)` has three non-cuspidal rational points.

WHAT THIS BUYS over the previous statement: the leaf is now a
DIOPHANTINE statement about an explicit plane curve, in the same shape
as the elementary descents this file already carries out
(`MazurTwoTwelve.Quartic`), rather than a statement about torsion that
first has to be transported. -/
theorem WeierstrassCurve.x1Eleven_plane_ne_zero (b c : ℚ)
    [(WeierstrassCurve.tateNormalForm b c).IsElliptic] (hb : b ≠ 0) :
    -b ^ 5 + 3 * c * b ^ 4 + (4 * c ^ 3 - 3 * c ^ 2) * b ^ 3
      + (-3 * c ^ 5 - 9 * c ^ 4 + c ^ 3) * b ^ 2
      + (c ^ 7 + 3 * c ^ 6 + 6 * c ^ 5) * b - c ^ 6 ≠ 0 :=
  sorry

/-- **`X_1(13)` has no non-cuspidal rational point, as a plane curve of
bidegree `(7, 10)`** (sorry node — level `13` of the seven-level node
below, in the explicit `(b, c)`-coordinates).

The polynomial is `F₁₃`, the cofactor of `b⁵⁶` in
`MazurX1Plane.eval_thirteen`; as for level `11`, `F₁₃(b, c) = 0` with
`b ≠ 0` says exactly that the origin of `tateNormalForm b c` has order
`13`.

`X_1(13)` has genus `2` and its Jacobian is `ℚ`-simple of dimension `2`
with `LRatio(J, 1) = 1/361 ≠ 0`, hence Mordell–Weil rank `0`; its six
rational points are its `φ(13)/2 = 6` rational cusps, and
`min_p #X_1(13)(𝔽_p) = 6` matches. Mazur–Tate, "Points of order 13 on
elliptic curves" (Invent. Math. 22, 1973); subsumed in Mazur 1977,
Thm 7. As at level `11` the `X_0` shortcut is unavailable, `13` being in
Kenku's list. -/
theorem WeierstrassCurve.x1Thirteen_plane_ne_zero (b c : ℚ)
    [(WeierstrassCurve.tateNormalForm b c).IsElliptic] (hb : b ≠ 0) :
    b ^ 7 - 6 * c * b ^ 6 + (4 * c ^ 3 + 15 * c ^ 2) * b ^ 5
      + (-9 * c ^ 5 - 15 * c ^ 4 - 20 * c ^ 3) * b ^ 4
      + (5 * c ^ 7 + 24 * c ^ 6 + 21 * c ^ 5 + 15 * c ^ 4) * b ^ 3
      + (-c ^ 9 - 6 * c ^ 8 - 21 * c ^ 7 - 13 * c ^ 6 - 6 * c ^ 5) * b ^ 2
      + (6 * c ^ 8 + 3 * c ^ 7 + c ^ 6) * b + c ^ 10 ≠ 0 :=
  sorry

/-- **The four residual rank-zero levels `17, 19, 25, 27`, in plane
form** (sorry node — the residue of the seven-level node below after
levels `11`, `13` are cut off as explicit plane curves and level `21` is
discharged outright).

STATEMENT. If the level-`N` value `wₙ = preΨ'ₙ(0)` vanishes on
`tateNormalForm b c`, then so does `w_d` for some `0 < d < N`. By the
PROVEN dictionary `MazurX1Plane.zsmul_eq_zero_iff` this says: the origin
never has order EXACTLY `N`, only possibly a proper divisor of it.

WHY IT IS TRUE, level by level, and why the `d`-clause is not optional:

* `N = 17, 19` (prime): `w_N = 0` means the origin has order `N`, which
  Mazur excludes; the hypothesis is unsatisfiable and any `d` will do.
  Plane models: `F₁₇` has bidegree `(12, 18)`, `F₁₉` bidegree `(15, 22)`
  — written out they are `~60` and `~90` terms, which is why they are
  left in `preΨ'` form here rather than expanded like `F₁₁` and `F₁₃`.
* `N = 25`: `w₂₅ = 0` means the order DIVIDES `25`, i.e. is `5` or `25`.
  Order `5` really does occur — `X_1(5)` has genus `0` and `w₅ = 0` is
  the line `b = c` (`MazurX1Plane.eval_five`) — so the conclusion `d = 5`
  is the true content and the statement WOULD BE FALSE without the
  `d`-clause. This is the trap that makes `w_N ≠ 0` the wrong shape for
  composite levels.
* `N = 27`: `w₂₇ = 0` means the order divides `27`. Order `3` forces
  `Ψ₃(0) = −b³ = 0`, impossible; so the order is `9` or `27`, and `27`
  being excluded leaves `d = 9`.

BOOKKEEPING NOTE for whoever takes this leaf. The `N = 27` case is
ALREADY PROVEN independently further down this file, at
`WeierstrassCurve.no_torsion_order_27` — via the `X_0(27)` route
(`j_of_stable_cyclic_subgroup_order_27`, `no_torsion_order_27_of_j`),
which needs no modular curve of level `27` at all. It is included here
only because `no_torsion_order_27_of_j` is declared BELOW this node and
Lean's declaration order forbids using it above.

**The repair is now cheap, and its feasibility was verified on
2026-07-26.** Half of the obstruction is already gone: the `X_0(27)`
cluster ending in `j_of_stable_cyclic_subgroup_order_27` was hoisted to
the top of this file that day (to unblock level `81`), so it is now far
ABOVE this node. What is still below is only the `MazurLevel27` CM-line
block and `no_torsion_order_27_of_j` / `no_torsion_order_27`, roughly
`600` lines down, and that block's backward dependencies are
`MazurLevel18.{order_three_of_a₂_eq_zero, psi3_eq_zero, exists_param}`
and `MazurLevel9.{cFour_cube_eq, jInvariant_of_variableChange}` — ALL of
which are already above this node. So that block can be hoisted here
verbatim, after which the `27` disjunct can simply be dropped from this
leaf. It was left alone because dropping the disjunct also restates this
leaf and its four consumers, which belong to another owner.

CITATION for the three that remain: Mazur 1977, Thm 7; the ranks are
`0` because every `ℚ`-simple factor of `J_1(N)` has `L(A, 1) ≠ 0`
(`LRatio`: `17: 1/16, 1/21316`; `19: 1/9, 1/2134521`;
`25: 1/5041, 1/10272025`), and `min_p #X_1(N)(𝔽_p) = φ(N)/2` equals the
number of rational cusps (`8, 9, 10`). See the seven-level node's
docstring below for the full audit. -/
theorem WeierstrassCurve.tateNormalForm_origin_preΨ'_residual (N : ℕ)
    (hN : N = 17 ∨ N = 19 ∨ N = 25 ∨ N = 27) (b c : ℚ)
    [(WeierstrassCurve.tateNormalForm b c).IsElliptic]
    (h00 : (WeierstrassCurve.tateNormalForm b c).toAffine.Nonsingular 0 0)
    (h : ((WeierstrassCurve.tateNormalForm b c).preΨ' N).eval 0 = 0) :
    ∃ d : ℕ, 0 < d ∧ d < N ∧
      ((WeierstrassCurve.tateNormalForm b c).preΨ' d).eval 0 = 0 :=
  sorry

/-- **`X_1(N)(ℚ)` is cuspidal at the seven rank-zero levels: in Tate
coordinates the origin never has order `N`, for
`N ∈ {11, 13, 17, 19, 21, 25, 27}`** (sorry node — ONE literature
citation for SEVEN levels; GENERALISED from the level-`25` node
2026-07-26, whose audit this docstring is and remains).

WHY THESE SEVEN AND NOT OTHERS. The proof is the same theorem at each,
and it is the one described in the REFUTED block below: `X_1(N)/ℚ` with
its rational cusps, `rank J_1(N)(ℚ) = 0` (from `L(A, 1) ≠ 0` for every
`ℚ`-simple factor `A`, via Kolyvagin–Logachev or Kato), and injectivity
of torsion under reduction at a good odd prime. It applies exactly when
BOTH inputs hold, and both were re-verified independently with Magma on
2026-07-26 (untrusted searcher; statement check only, never a proof):

* every `ℚ`-simple factor of `J_1(N)` has `LRatio(A, 1) ≠ 0` for
  `N ∈ {11, 13, 17, 19, 21, 25, 27}` — the factor dimensions and ratios
  are `11`: `(1, 1/25)`; `13`: `(2, 1/361)`; `17`: `(1, 1/16), (4,
  1/21316)`; `19`: `(1, 1/9), (6, 1/2134521)`; `21`: `(1, 1/8), (2,
  1/169), (2, 1/49)`; `25`: `(4, 1/5041), (8, 1/10272025)`; `27`:
  `(1, 1/9), (12, 1/8267805027)`;
* `min_p #X_1(N)(𝔽_p) = φ(N)/2 = #(rational cusps)` at each, with
  `#X_1(N)(𝔽_p) = p + 1 − Tr(T_p ∣ S_2(Γ_1(N)))`: the minima are
  `5, 6, 8, 9, 6, 10, 9` and the genera `1, 2, 5, 7, 5, 12, 13`.

Embedding `X_1(N)(ℚ) ↪ J_1(N)(ℚ)` at a rational cusp and reducing at a
good odd prime realising the minimum is then injective on the finite
group `J_1(N)(ℚ)`, so `#X_1(N)(ℚ) ≤ φ(N)/2`, which the rational cusps
already exhaust. Hence every rational point is a cusp — which IS this
node.

**IT BREAKS AT `37`, AND EXACTLY THERE.** `J_1(37)` has a factor of
dimension `1` with `LRatio(1) = 0` (the elliptic curve `37a`, of rank
`1`), alongside seven factors with `LRatio ≠ 0`. So the whole-Jacobian
argument fails and levels `37, 43, 67, 163` need the winding /
Eisenstein quotient instead — they are deliberately NOT in the
hypothesis of this node. Levels `16, 18, 24` satisfy the `L(1) ≠ 0`
half but not the point-count half, and are anyway already closed
elementarily elsewhere in this file.

Of the seven, `21` and `27` are at present closed in this file by other
routes (`no_torsion_order_21`'s structural argument and
`no_torsion_order_27_of_j`, Olson's CM theorem), so the levels this node
is *currently* wired to serve are `11, 13, 17, 19, 25` — but the
statement is proved for all seven at once, and the two extra levels cost
nothing.

Everything below is the level-`25` audit, kept verbatim because it is
the instance where the seven-level structure was found.

`X_1(25)` has genus
`12` and no non-cuspidal
rational point (subsumed in Mazur 1977, Thm 8). The `X_0` shortcut is
NOT available at this level: a rational cyclic `25`-isogeny does exist
(the class `11a` contains one), so `X_0(25)` has non-cuspidal rational
points and only the `X_1` statement excludes an order-`25` point.

IRREDUCIBLE at this mathlib pin — meaning no OTHER node of this file
implies it, which is still true; but NOT "no shallower node exists",
which was the 2026-07-25 verdict and is refuted below (audit
2026-07-25, re-audited the same
day when level `27` — the other level of Kenku's list where `X_0` still
bites — was reduced to its `X_0(27)` `j`-determination). The
genus `12` is the standard formula
`g(X_1(N)) = 1 + (N²/24)∏_{p ∣ N}(1 − p⁻²) − ¼ Σ_{d ∣ N} φ(d)φ(N/d)`
evaluated at `N = 25` (recomputed 2026-07-25). Routes checked and
rejected:

* *The `X_0` route that closes `27` and `49` has no analogue here.*
  `X_0(25)` has genus `0`, so its rational points are a rational
  one-parameter family and a rational cyclic `25`-subgroup puts NO
  constraint on `j(E)` — unlike level `27`, where `X_0(27)` is a
  rank-`0` genus-`1` curve with a single non-cuspidal rational point.
  Verified with PARI/GP: `ellisomat` on `11a1 = [0,-1,1,-10,-20]`
  returns the degree matrix `[1,5,5; 5,1,25; 5,25,1]`, so a rational
  cyclic `25`-isogeny genuinely exists.
* *Divisor reduction fails by design.* The proper divisors of `25` are
  `1` and `5`, both in Mazur's allowed set, so nothing here implies the
  node.
* *Reduction plus Hasse fails, even in its sharp congruence form.* A
  rational point of order `25` makes the mod-`25` representation
  `(1 ∗; 0 ω)` (the rational cyclic subgroup is the trivial character,
  and the determinant is cyclotomic), so `a_p ≡ 1 + p (mod 25)` at
  every prime `p ≠ 5` of good reduction, while `|a_p| ≤ 2√p`. That
  congruence is strictly stronger than the bare bound `25 ≤ p+1+2√p`,
  but at this level it forces exactly the same thing: bad reduction at
  `p ∈ {2, 3, 7, 11, 13}` and nothing at any `p ≥ 17` (checked to
  `p < 400` with PARI/GP). A conductor lower bound is not a
  contradiction — curves of every such conductor exist.

A formal proof needs `X_1(25)` as an arithmetic curve over `ℚ` together
with a determination of its rational points (Chabauty/Kenku-style, or
the Eisenstein-ideal descent). The one structural observation worth
recording for a future attack: if `P` has order `25` then
`E' = E/⟨5P⟩` carries the rational point `φ(P)` of order `5` AND the
rational subgroup `ker φ̂` of order `5`, and these are independent
(`P ∉ E[5]`), so `E'[5] ≅ ℤ/5 ⊕ μ_5` as a Galois module. That is a
level-`25` structure again, not a simplification — but it is the shape
in which the classical proofs proceed.

RE-AUDITED 2026-07-25 against the route that closed level `27`
(`no_torsion_order_27_of_j`), and it does NOT transfer. That proof works
because a point of order `27` yields a point of order `9`, and `X_1(9)`
has genus `0`: the Tate normal form is then a rational LINE
(`c = d²(d − 1)`, `b = c(d² − d + 1)`), on which the extra hypothesis —
there, a prescribed `j`-invariant — becomes a one-variable polynomial
equation that can be refuted by a congruence. Here the descent by one
prime power gives only a point of order `5`, i.e. the genus-`0` line
`b = c` of `X_1(5)`; but the residual condition that the order-`5` point
be `5` times a rational point of order `25` is `X_1(25)` itself, and
there is no auxiliary hypothesis (no `j`-invariant, no isogeny
obstruction — see the `X_0(25)` bullet above) to cut it down to a curve
of genus `0`. That much stands.

**REFUTED 2026-07-26: "the only intermediate quotient is the genus-`0`
one, so `25` is the only level of the eleven with no shallower node".**
Both halves are wrong, and what replaces them is a complete classical
proof with every number checked. All computations below are Magma —
untrusted searcher, statement check only, never a proof.

* *There IS a genus-`4` intermediate curve.* The diamond group is
  `(ℤ/25)^× / ±1 ≅ ℤ/10`, so the curves between `X_1(25)` and `X_0(25)`
  are the `X_Δ(25)` for the subgroups `Δ ⊆ (ℤ/25)^×` containing `−1`:
  `{±1}`, `⟨7⟩ = {±1, ±7}`, the squares, and everything. Each genus is
  `Σ_χ dim S_2(25, χ)` over the `χ` trivial on `Δ`, and
  `dim S_2(25, χ) = 0, 0, 1, 2` for `χ` even of order `1, 2, 5, 10`
  (total `0 + 0 + 4·1 + 4·2 = 12 = g(X_1(25))` ✓). So the four genera
  are `12`, **`4`**, `0`, `0`. The earlier audit found the genus-`0`
  quotient and stopped; the genus-`4` curve `X_{⟨7⟩}(25)` — a point of
  order `25` remembered up to `P ↦ ±P, ±7P` — was missed.
  Confirmed twice more, independently of modular symbols. (i) The
  congruence-subgroup genus formula: `Γ_{⟨7⟩}(25)` has index
  `[SL₂(ℤ) : Γ_1(25)]/|⟨7⟩| = 600/4 = 150` in `PSL₂(ℤ)` (unchanged by
  `±`, as `−I ∈ Γ_{⟨7⟩}`), `ν₂ = 10`, `ν₃ = 0`, `ν_∞ = 14`, giving
  `1 + 150/12 − 10/4 − 14/2 = 4`. (ii) Riemann–Hurwitz for the
  degree-`2` diamond quotient `X_1(25) → X_{⟨7⟩}(25)`: `⟨7⟩` fixes
  `(E, P)` exactly when some automorphism `α` of `E` has `αP = 7P`,
  which forces `α = i` and `j = 1728` (since `7² = 49 ≡ −1 mod 25`),
  and there are `10` such points; `2·12 − 2 = 2(2g − 2) + 10` gives
  `g = 4`.
* *`J_1(25)` has Mordell–Weil rank `0`.* It is `ℚ`-isogenous to
  `A₄ × A₈`, of dimensions `4` and `8` (the quintic- and
  order-`10`-character parts), and `L(A, 1) ≠ 0` for BOTH:
  `LRatio(A, 1) = 1/5041` and `1/10272025`. By Kolyvagin–Logachev
  (or Kato) the rank is `0`, so `J_1(25)(ℚ)` is FINITE.
  `Jac X_{⟨7⟩}(25) = A₄`, hence also rank `0`.
* *The point count then closes the level outright — no Chabauty.*
  `X_1(25)` has good reduction away from `5`, and
  `#X_1(25)(𝔽_p) = p + 1 − Tr(T_p ∣ S_2(Γ_1(25))) = 10` for
  `p = 2, 3, 7, 13`. Its rational cusps are exactly the `φ(25)/2 = 10`
  carried by the Néron `25`-gon (the point of order `25` meets every
  component, so the pair is rational); the `10` on the `1`-gon `𝔾_m`
  have `P ∈ μ₂₅` and form ONE Galois orbit over `ℚ(ζ₂₅)⁺`, and the `8`
  of denominator `5` lie over the irrational denominator-`5` cusps of
  `X_0(25)`. Embedding `X_1(25)(ℚ) ↪ J_1(25)(ℚ)` at a rational cusp and
  reducing at the odd good prime `3` (injective on torsion) gives
  `#X_1(25)(ℚ) ≤ #X_1(25)(𝔽_3) = 10 = #(rational cusps)`. So every
  rational point is a cusp — which IS this node. The genus-`4` quotient
  gives the same conclusion independently:
  `#X_{⟨7⟩}(25)(𝔽_3) = #X_{⟨7⟩}(25)(𝔽_13) = 5`, and it has exactly `5`
  rational cusps (`⟨7⟩/±` acts freely on the `10`, since `7P = ±P` is
  impossible for `P` of order `25`, and the other cusp orbits stay
  irrational because they stay irrational already on `X_0(25)` or are
  permuted transitively by `Gal(ℚ(ζ₂₅)⁺/ℚ)`).
* *Cross-check that the pipeline is sound.* The identical computation
  returns `#X_1(11)(𝔽_3) = 5 = φ(11)/2` and `#X_1(13)(𝔽_3) = 6 =
  φ(13)/2`, reproducing Billing–Mahler and Mazur–Tate exactly.
* *Cross-check of the genus-`4` claim itself.* It predicts that the
  `11a` cyclic `25`-isogeny does NOT give a non-cuspidal rational point
  of `X_{⟨7⟩}(25)`: its kernel character must have order `5`, `10` or
  `20`, not dividing `4`. Since the only cyclic quartic field
  unramified outside `{5, 11}` is `ℚ(ζ₅)`, that is testable, and it
  holds — the torsion of `11a1, 11a2, 11a3` over `ℚ(ζ₅)` is
  `ℤ/5 × ℤ/5`, `ℤ/5`, `ℤ/5`, with no `25`-torsion anywhere. (This also
  corrects the old text: the cyclic `25`-isogeny of the class joins
  `11a2` and `11a3`; `11a1` itself has only the two `5`-isogenies, and
  its `ℤ/5 × ℤ/5` over `ℚ(ζ₅)` is exactly the split `ℤ/5 ⊕ μ₅` that
  makes the class work.)

**THIS IS ONE MISSING THEORY FOR SEVEN LEVELS, NOT ONE.** Every
`ℚ`-simple factor of `J_1(N)` has `L(1) ≠ 0` for
`N ∈ {11, 13, 16, 17, 18, 19, 21, 24, 25, 27}`, and
`min_p #X_1(N)(𝔽_p) = φ(N)/2 = #(rational cusps)` for
`N ∈ {11, 13, 17, 19, 21, 25, 27}`. So the single theory — `X_1(N)/ℚ`
with its cusps, `rank J_1(N)(ℚ) = 0` from `L(1) ≠ 0`, and injectivity
of torsion under good reduction — closes levels
`11, 13, 17, 19, 21, 25, 27` in one blow, i.e. seven of this file's
sorried nodes rather than this one. It breaks at `37` in a precisely
identifiable place: `J_1(37)` has a rank-`1` factor (`LRatio(1) = 0`,
the elliptic curve `37a`), so `37, 43, 67, 163` need the
winding/Eisenstein quotient instead of the whole Jacobian. None of it
exists here: `grep ModularCurve` over mathlib returns nothing, and
`~/cs/FLT` takes the Mazur bound as a bare `axiom`.

STATED IN TATE COORDINATES (2026-07-26), matching levels `11, 13, 17,
19, 37, 43, 67, 163`. The general form of this level — no rational
point of order `25` on ANY elliptic curve over `ℚ` — is
`no_torsion_order_25` just below, and is PROVEN from this node. Here
the curve is the explicit two-parameter family `tateNormalForm b c` and
the point is the origin, so this node IS the plane model of `X_1(25)`
in the `(b, c)`-coordinates rather than a statement quantified over all
curves. The passage between the two is the PROVEN
`exists_tateNormalForm`; everything above about genus, witnesses and
citation is unchanged by the restatement.

GENERALISED 2026-07-26. The whole of the above is now a corollary of the
single node `tateNormalForm_origin_order_ne_of_cuspidalRankZero`
immediately below, which states it uniformly for the SEVEN levels whose
proof is the same theorem. That node, not this one, is where the work
is; this one is PROVEN from it by instantiating `N := 25`.

DECOMPOSED AND PARTLY PROVEN 2026-07-26. The node itself is no longer a
`sorry`: it is now derived, level by level, from the plane model of
`X_1(N)` in the `(b, c)`-coordinates (section `MazurX1Plane` above,
PROVEN) together with three shallower nodes. The cut is:

* `N = 21` is **PROVEN OUTRIGHT** here, from the file's own
  `no_torsion_order_21` — the `X_0(21)` + genus-`0` `X_1(7)` route,
  which involves no rank-`0` Jacobian input at all. So level `21` was
  never part of the "same theorem" this node claims to state uniformly:
  it was already free, and grouping it with the others overstated the
  citation. That is a correction to the audit below, not a change of
  statement.
* `N = 11, 13` go to `x1Eleven_plane_ne_zero` and
  `x1Thirteen_plane_ne_zero`: the EXPLICIT affine plane curves
  `F₁₁(b, c) = 0` (bidegree `(5, 7)`) and `F₁₃(b, c) = 0` (bidegree
  `(7, 10)`), which are the `(b, c)`-models of `X_1(11)` and `X_1(13)`.
* `N = 17, 19, 25, 27` go to `tateNormalForm_origin_preΨ'_residual`,
  stated in `preΨ'` form because those plane curves are too large to
  write out (`~60`, `~90`, and several hundred terms). Its docstring
  records that the `27` case is already proven independently below, and
  is present only because of Lean's declaration order.

The transport is the PROVEN division-polynomial torsion dictionary
`TorsionCard.smul_some_eq_zero_iff`, specialised to the origin: the
`normEDS` recursion behind mathlib's `preΨ'` is closed under evaluation
at a fixed `x`, so `preΨ'ₙ(0)` is a polynomial in `(b, c)` computable
from `Ψ₂Sq(0) = b²`, `Ψ₃(0) = −b³`, `preΨ₄(0) = −b⁴c`. Every level
value used below is DERIVED inside Lean from that recursion, so the
explicit polynomials are machine-checked rather than asserted.

FAITHFULNESS NOTE, and it is the trap of this cut. The seemingly
natural residual statement `preΨ'_N(0) ≠ 0` is FALSE at the composite
levels: `preΨ'₂₅(0) = 0` says the order DIVIDES `25`, and order `5` is
everywhere on this family (`preΨ'₅(0) = b⁸(b − c)`, the genus-`0` line
`b = c`). The residual node therefore concludes with a proper divisor
`d`, not with non-vanishing. -/
theorem WeierstrassCurve.tateNormalForm_origin_order_ne_of_cuspidalRankZero
    (N : ℕ)
    (hN : N = 11 ∨ N = 13 ∨ N = 17 ∨ N = 19 ∨ N = 21 ∨ N = 25 ∨ N = 27)
    (b c : ℚ)
    [(WeierstrassCurve.tateNormalForm b c).IsElliptic]
    (h00 : (WeierstrassCurve.tateNormalForm b c).toAffine.Nonsingular 0 0) :
    addOrderOf (Affine.Point.some 0 0 h00) ≠ N := by
  intro hord
  have hb : b ≠ 0 := MazurX1Plane.b_ne_zero h00
  -- forward: the order condition makes the level polynomial vanish
  have key : ∀ n : ℕ, ¬ Even n → addOrderOf (Affine.Point.some 0 0 h00) = n →
      ((WeierstrassCurve.tateNormalForm b c).preΨ' n).eval 0 = 0 := by
    intro n hodd hn
    have hn0 : (n : ℤ) ≠ 0 := by
      rintro h0
      rw [show n = 0 from by exact_mod_cast h0] at hodd
      exact hodd (by decide)
    have hz : (n : ℤ) • (Affine.Point.some 0 0 h00) = 0 := by
      rw [natCast_zsmul, ← hn]; exact addOrderOf_nsmul_eq_zero _
    have hΨ :=
      (MazurX1Plane.zsmul_eq_zero_iff (WeierstrassCurve.tateNormalForm b c) h00 hn0).mp hz
    rw [MazurX1Plane.eval_ΨSq_odd _ _ n hodd] at hΨ
    exact pow_eq_zero_iff two_ne_zero |>.mp hΨ
  -- backward: a level value vanishing at a smaller index bounds the order
  have back : ∀ d : ℕ, 0 < d →
      ((WeierstrassCurve.tateNormalForm b c).preΨ' d).eval 0 = 0 →
      addOrderOf (Affine.Point.some 0 0 h00) ≤ d := by
    intro d hd hdz
    have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
    have hz : (d : ℤ) • (Affine.Point.some 0 0 h00) = 0 :=
      (MazurX1Plane.zsmul_eq_zero_iff (WeierstrassCurve.tateNormalForm b c) h00 hd0).mpr
        (MazurX1Plane.eval_ΨSq_of_preΨ' _ _ d hdz)
    rw [natCast_zsmul] at hz
    exact Nat.le_of_dvd hd (addOrderOf_dvd_of_nsmul_eq_zero hz)
  rcases hN with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- `N = 11`: the plane quintic `F₁₁`
    have h := key 11 (by decide) hord
    rw [MazurX1Plane.eval_eleven] at h
    rcases mul_eq_zero.mp h with h0 | h0
    · exact hb (pow_eq_zero_iff (by norm_num) |>.mp h0)
    · exact WeierstrassCurve.x1Eleven_plane_ne_zero b c hb h0
  · -- `N = 13`: the plane curve `F₁₃`
    have h := key 13 (by decide) hord
    rw [MazurX1Plane.eval_thirteen] at h
    rcases mul_eq_zero.mp h with h0 | h0
    · exact hb (pow_eq_zero_iff (by norm_num) |>.mp h0)
    · exact WeierstrassCurve.x1Thirteen_plane_ne_zero b c hb h0
  · -- `N = 17`
    obtain ⟨d, hd0, hdN, hdz⟩ :=
      WeierstrassCurve.tateNormalForm_origin_preΨ'_residual 17 (by tauto) b c h00
        (key 17 (by decide) hord)
    have hle := back d hd0 hdz
    rw [hord] at hle
    omega
  · -- `N = 19`
    obtain ⟨d, hd0, hdN, hdz⟩ :=
      WeierstrassCurve.tateNormalForm_origin_preΨ'_residual 19 (by tauto) b c h00
        (key 19 (by decide) hord)
    have hle := back d hd0 hdz
    rw [hord] at hle
    omega
  · -- `N = 21`: PROVEN, from the `X_0(21)` + `X_1(7)` route above
    exact WeierstrassCurve.no_torsion_order_21 (WeierstrassCurve.tateNormalForm b c)
      (Affine.Point.some 0 0 h00) hord
  · -- `N = 25`
    obtain ⟨d, hd0, hdN, hdz⟩ :=
      WeierstrassCurve.tateNormalForm_origin_preΨ'_residual 25 (by tauto) b c h00
        (key 25 (by decide) hord)
    have hle := back d hd0 hdz
    rw [hord] at hle
    omega
  · -- `N = 27`
    obtain ⟨d, hd0, hdN, hdz⟩ :=
      WeierstrassCurve.tateNormalForm_origin_preΨ'_residual 27 (by tauto) b c h00
        (key 27 (by decide) hord)
    have hle := back d hd0 hdz
    rw [hord] at hle
    omega

/-- **No rational point of order `25`** (PROVEN 2026-07-26 by
instantiating the seven-level node above at `N = 25`). All the
mathematical content, the citation and the audit are in that node's
docstring and in this one; nothing is specific to `25` any more. -/
theorem WeierstrassCurve.tateNormalForm_origin_order_ne_25 (b c : ℚ)
    [(WeierstrassCurve.tateNormalForm b c).IsElliptic]
    (h00 : (WeierstrassCurve.tateNormalForm b c).toAffine.Nonsingular 0 0) :
    addOrderOf (Affine.Point.some 0 0 h00) ≠ 25 :=
  WeierstrassCurve.tateNormalForm_origin_order_ne_of_cuspidalRankZero 25
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) b c h00

/-- **No rational point of order `25`** (PROVEN 2026-07-26 from the
Tate-coordinate node above through `no_torsion_order_of_tateNormalForm`):
a point of order `25 ≥ 4` puts its curve in Tate normal form at the
origin, so the general statement follows from the one about the
explicit family. All the mathematical content is in the node above,
whose docstring carries this level's citation and audit. -/
theorem WeierstrassCurve.no_torsion_order_25 (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (Q : (E⁄ℚ).Point) : addOrderOf Q ≠ 25 :=
  WeierstrassCurve.no_torsion_order_of_tateNormalForm (by norm_num)
    (fun b c hell h00 =>
      @WeierstrassCurve.tateNormalForm_origin_order_ne_25 b c hell h00) E Q

namespace MazurLevel27

/-! ### The CM `j`-invariant along the `X_1(9)` line

The three lemmas below carry out, as pure arithmetic, the computation
that closes `no_torsion_order_27_of_j`. Write `E(b, c)` for the Tate
normal form and impose `9 • (0,0) = 0`; by `MazurLevel18.exists_param`
this is the rational line `c = d²(d − 1)`, `b = c(d² − d + 1)`, and
along it (`MazurLevel18.delta_param`)

  `Δ = d⁹(d − 1)⁹(d² − d + 1)³(d³ − 6d² + 3d + 1)`,
  `c₄ = ((1 − c)² − 4b)² + 24(1 − c)b`  (degree `12` in `d`).

So `j = −12288000` is the single equation `c₄³ + 12288000 Δ = 0`, a
polynomial of degree `36` in `d` — the fibre of `j : X_1(9) → X(1)` over
the CM point of discriminant `−27`. It has NO rational root, and the
proof is a two-element congruence: homogenise `d = N/E` with
`gcd(N, E) = 1`, and observe that modulo `2` the coefficient `12288000`
dies, while

  `c₄ ≡ (N³ + N²E + E³)⁴ (mod 2)`,

so the equation forces `N³ + N²E + E³ ≡ 0 (mod 2)`, which fails in each
of the three admissible parities. (PARI/GP, untrusted searcher: the
degree-`36` polynomial factors as
`(d³ + 3d² − 6d + 1)(d⁶ − 12d⁵ + 69d⁴ − 88d³ + 24d² + 6d + 1)` times an
irreducible degree-`27` factor, all three monic with constant term `1`,
so the rational-root theorem gives the same conclusion; `p = 2` is used
here because it needs four case evaluations rather than `37`
coefficients.) -/

/-- **The `mod 2` obstruction** (PROVEN by `decide`): the homogeneous
degree-`36` form `c₄(N, E)³ + 12288000 E⁹ Δ(N, E)` is odd at every pair
of residues other than `(0, 0)`. -/
lemma jEquation_zmodTwo : ∀ n e : ZMod 2, ¬ (n = 0 ∧ e = 0) →
    ((((e ^ 3 - n ^ 2 * (n - e)) ^ 2
          - 4 * e * (n ^ 2 * (n - e) * (n ^ 2 - n * e + e ^ 2))) ^ 2
        + 24 * e ^ 4 * ((e ^ 3 - n ^ 2 * (n - e)) * (n ^ 2 * (n - e) * (n ^ 2 - n * e + e ^ 2)))) ^ 3
      + 12288000 * e ^ 9 *
        (n ^ 9 * (n - e) ^ 9 * (n ^ 2 - n * e + e ^ 2) ^ 3
          * (n ^ 3 - 6 * n ^ 2 * e + 3 * n * e ^ 2 + e ^ 3))) ≠ 0 := by
  decide

/-- **The homogeneous form has no primitive integral zero** (PROVEN):
immediate from `jEquation_zmodTwo` by reduction modulo `2`. -/
lemma jEquation_int (N E : ℤ) (h2 : ¬ ((2 : ℤ) ∣ N ∧ (2 : ℤ) ∣ E)) :
    ((((E ^ 3 - N ^ 2 * (N - E)) ^ 2
          - 4 * E * (N ^ 2 * (N - E) * (N ^ 2 - N * E + E ^ 2))) ^ 2
        + 24 * E ^ 4 * ((E ^ 3 - N ^ 2 * (N - E)) * (N ^ 2 * (N - E) * (N ^ 2 - N * E + E ^ 2)))) ^ 3
      + 12288000 * E ^ 9 *
        (N ^ 9 * (N - E) ^ 9 * (N ^ 2 - N * E + E ^ 2) ^ 3
          * (N ^ 3 - 6 * N ^ 2 * E + 3 * N * E ^ 2 + E ^ 3))) ≠ 0 := by
  intro hz
  refine jEquation_zmodTwo (N : ZMod 2) (E : ZMod 2) ?_ ?_
  · rintro ⟨hn, he⟩
    exact h2 ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd N 2).mp hn,
      (ZMod.intCast_zmod_eq_zero_iff_dvd E 2).mp he⟩
  · have := congrArg (fun z : ℤ => (z : ZMod 2)) hz
    push_cast at this
    exact this

/-- **`j = −12288000` has no solution on the `X_1(9)` line** (PROVEN):
the degree-`36` equation in the Kubert parameter `d`, cleared of
denominators against `d = num/den`, is exactly the homogeneous form of
`jEquation_int` at the coprime pair `(d.num, d.den)`. -/
lemma jEquation_rat (d : ℚ)
    (hj : (((1 - d ^ 2 * (d - 1)) ^ 2 - 4 * (d ^ 2 * (d - 1) * (d ^ 2 - d + 1))) ^ 2
        + 24 * ((1 - d ^ 2 * (d - 1)) * (d ^ 2 * (d - 1) * (d ^ 2 - d + 1)))) ^ 3
      + 12288000 * (d ^ 9 * (d - 1) ^ 9 * (d ^ 2 - d + 1) ^ 3
        * (d ^ 3 - 6 * d ^ 2 + 3 * d + 1)) = 0) : False := by
  have hd0 : ((d.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr d.den_nz
  have hcop : ¬ ((2 : ℤ) ∣ d.num ∧ (2 : ℤ) ∣ (d.den : ℤ)) := by
    rintro ⟨h1, h2⟩
    have h1' : 2 ∣ d.num.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr h1
    have h2' : 2 ∣ d.den := by exact_mod_cast h2
    have := Nat.dvd_gcd h1' h2'
    rw [d.reduced] at this
    omega
  refine jEquation_int d.num (d.den : ℤ) hcop ?_
  have hNq : ((d.num : ℚ)) = d * ((d.den : ℚ)) := (div_eq_iff hd0).mp (Rat.num_div_den d)
  have key : (((((d.den : ℤ) ^ 3 - d.num ^ 2 * (d.num - (d.den : ℤ))) ^ 2
          - 4 * (d.den : ℤ) * (d.num ^ 2 * (d.num - (d.den : ℤ))
              * (d.num ^ 2 - d.num * (d.den : ℤ) + (d.den : ℤ) ^ 2))) ^ 2
        + 24 * (d.den : ℤ) ^ 4 * (((d.den : ℤ) ^ 3 - d.num ^ 2 * (d.num - (d.den : ℤ)))
            * (d.num ^ 2 * (d.num - (d.den : ℤ))
              * (d.num ^ 2 - d.num * (d.den : ℤ) + (d.den : ℤ) ^ 2)))) ^ 3
      + 12288000 * (d.den : ℤ) ^ 9 *
        (d.num ^ 9 * (d.num - (d.den : ℤ)) ^ 9
          * (d.num ^ 2 - d.num * (d.den : ℤ) + (d.den : ℤ) ^ 2) ^ 3
          * (d.num ^ 3 - 6 * d.num ^ 2 * (d.den : ℤ) + 3 * d.num * (d.den : ℤ) ^ 2
              + (d.den : ℤ) ^ 3)) : ℤ) = 0 := by
    have hq : ((((((d.den : ℤ) ^ 3 - d.num ^ 2 * (d.num - (d.den : ℤ))) ^ 2
          - 4 * (d.den : ℤ) * (d.num ^ 2 * (d.num - (d.den : ℤ))
              * (d.num ^ 2 - d.num * (d.den : ℤ) + (d.den : ℤ) ^ 2))) ^ 2
        + 24 * (d.den : ℤ) ^ 4 * (((d.den : ℤ) ^ 3 - d.num ^ 2 * (d.num - (d.den : ℤ)))
            * (d.num ^ 2 * (d.num - (d.den : ℤ))
              * (d.num ^ 2 - d.num * (d.den : ℤ) + (d.den : ℤ) ^ 2)))) ^ 3
      + 12288000 * (d.den : ℤ) ^ 9 *
        (d.num ^ 9 * (d.num - (d.den : ℤ)) ^ 9
          * (d.num ^ 2 - d.num * (d.den : ℤ) + (d.den : ℤ) ^ 2) ^ 3
          * (d.num ^ 3 - 6 * d.num ^ 2 * (d.den : ℤ) + 3 * d.num * (d.den : ℤ) ^ 2
              + (d.den : ℤ) ^ 3)) : ℤ) : ℚ) = 0 := by
      push_cast
      rw [hNq]
      linear_combination ((d.den : ℚ)) ^ 36 * hj
    exact_mod_cast hq
  exact key

/-- **`j · Δ = c₄³`** (PROVEN): the definition `j = Δ'⁻¹ c₄³` cleared of
its inverse, which is how the `j`-invariant hypothesis is turned into a
polynomial identity. -/
lemma cFour_cube_eq (W : WeierstrassCurve ℚ) [W.IsElliptic] : W.j * W.Δ = W.c₄ ^ 3 := by
  rw [← WeierstrassCurve.coe_Δ', WeierstrassCurve.j, mul_comm, ← mul_assoc, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, one_mul]

/-- **The `j`-invariant survives the Tate normal form** (PROVEN): if two
changes of variables carry `E⁄ℚ` to `E(b, c)` then `E` and `E(b, c)`
have the same `j`-invariant. Stated separately because
`WeierstrassCurve.j` carries an `IsElliptic` instance argument, so the
transport has to go through `simp_rw` (mathlib's own advice at the
definition of `j`). -/
lemma jInvariant_of_variableChange (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (C₁ C₂ : VariableChange ℚ) (b c : ℚ)
    [(⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve ℚ).IsElliptic]
    (hEq : C₂ • (C₁ • (E⁄ℚ)) = (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve ℚ)) :
    E.j = (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve ℚ).j := by
  haveI : (E⁄ℚ).IsElliptic := inferInstanceAs (E.map (algebraMap ℚ ℚ)).IsElliptic
  simp_rw [← hEq, variableChange_j]
  simp [WeierstrassCurve.baseChange]

/-- **No curve of `j`-invariant `−12288000` carries a rational point of
order `9`, in Tate coordinates** (PROVEN): the `(b, c)` form of the
level-`27` CM statement. Together `hc`, `hb` say that `(0,0)` has order
`9` on `E(b, c)` (`MazurLevel18.exists_param`), and `hj` says
`j(E(b,c)) = −12288000` in the denominator-free form `c₄³ + 12288000 Δ = 0`. -/
theorem no_jInvariant_of_order_nine (b c d : ℚ)
    (hc : c = d ^ 2 * (d - 1)) (hb : b = c * (d ^ 2 - d + 1))
    (hj : (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve ℚ).c₄ ^ 3
        + 12288000 * (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve ℚ).Δ = 0) : False := by
  refine jEquation_rat d ?_
  subst hb; subst hc
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.Δ, WeierstrassCurve.b₆, WeierstrassCurve.b₈] at hj
  linear_combination hj

end MazurLevel27

/-- **Tate normal form at a rational point of order `9`, recording the
`j`-invariant** (PROVEN 2026-07-25): the same construction as
`exists_tateNormalForm_of_order_nine`, whose conclusion is enlarged by
the `j`-invariant relation `j(E) · Δ(E(b,c)) = c₄(E(b,c))³`.

The two changes of variables are isomorphisms, so they preserve `j`;
the sibling theorem simply does not expose that, because its consumer
(`not_order_two_and_order_nine_point`) does not need it. This variant is
what `no_torsion_order_27_of_j` needs, since there the input is a
`j`-invariant and the output is a Diophantine condition on the Kubert
parameter. The relation is stated multiplied out, as
`E.j * Δ = c₄ ^ 3`, so that the statement does not have to carry an
`IsElliptic` instance for `E(b, c)`. -/
theorem WeierstrassCurve.exists_tateNormalForm_jInvariant_of_order_nine
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (Q : (E⁄ℚ).Point) (hQ : addOrderOf Q = 9) :
    ∃ (b c : ℚ) (_hb : b ≠ 0)
      (_hΔ : (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve ℚ).Δ ≠ 0)
      (h00 : (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve ℚ).toAffine.Nonsingular 0 0)
      (Ψ : (E⁄ℚ).Point ≃+ (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve ℚ).toAffine.Point),
      Ψ Q = Affine.Point.some 0 0 h00 ∧
        E.j * (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve ℚ).Δ
          = (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve ℚ).c₄ ^ 3 := by
  haveI : (E⁄ℚ).IsElliptic := inferInstanceAs (E.map (algebraMap ℚ ℚ)).IsElliptic
  -- coordinates of `Q`
  have hQ0 : Q ≠ 0 := by rintro rfl; simp at hQ
  obtain ⟨X, Y, hns, hQxy⟩ :
      ∃ (X Y : ℚ) (h : (E⁄ℚ).toAffine.Nonsingular X Y), Q = Affine.Point.some X Y h := by
    rcases hcase : Q with _ | ⟨X, Y, h⟩
    · exact absurd hcase hQ0
    · exact ⟨X, Y, h, rfl⟩
  -- `Q` is not `2`-torsion, so `2Y + a₁X + a₃ ≠ 0`
  have hQ2 : Q + Q ≠ 0 := by
    intro h
    have hd : addOrderOf Q ∣ 2 := addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by rw [two_nsmul]; exact h)
    rw [hQ] at hd; norm_num at hd
  have hwne : Y ≠ (E⁄ℚ).toAffine.negY X Y := fun h =>
    hQ2 (by rw [hQxy]; exact Point.add_self_of_Y_eq h)
  have ha3ne : (E⁄ℚ).a₃ + X * (E⁄ℚ).a₁ + 2 * Y ≠ 0 := by
    intro h; exact hwne (by rw [Affine.negY]; linarith [h])
  -- the translating/shearing change of variables
  set s₀ : ℚ := ((E⁄ℚ).a₄ + 2 * X * (E⁄ℚ).a₂ - Y * (E⁄ℚ).a₁ + 3 * X ^ 2)
      / ((E⁄ℚ).a₃ + X * (E⁄ℚ).a₁ + 2 * Y) with hs₀
  set C₁ : VariableChange ℚ := ⟨1, X, s₀, Y⟩ with hC₁
  have hE1a₃ : (C₁ • (E⁄ℚ)).a₃ = (E⁄ℚ).a₃ + X * (E⁄ℚ).a₁ + 2 * Y := by
    rw [WeierstrassCurve.variableChange_a₃, hC₁]; simp
  have hE1a₄ : (C₁ • (E⁄ℚ)).a₄ = 0 := by
    rw [WeierstrassCurve.variableChange_a₄, hC₁]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    rw [hs₀]
    field_simp
    ring
  have hE1a₆ : (C₁ • (E⁄ℚ)).a₆ = 0 := by
    have heq := hns.1
    rw [Affine.equation_iff] at heq
    rw [WeierstrassCurve.variableChange_a₆, hC₁]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    linear_combination -heq
  -- `(0,0)` is a nonsingular point of the sheared curve, and it corresponds to `Q`
  have h00' : (C₁ • (E⁄ℚ)).toAffine.Nonsingular 0 0 :=
    Affine.nonsingular_zero.mpr ⟨hE1a₆, Or.inl (by rw [hE1a₃]; exact ha3ne)⟩
  have hmap : Point.equivVariableChange (E⁄ℚ) C₁ (Point.some 0 0 h00') = Q := by
    rw [Point.equivVariableChange_some, hQxy]
    exact Point.some_eq_some _ (by simp [hC₁]) (by simp [hC₁])
  -- `a₂ ≠ 0` after the shear, else `(0,0)` — hence `Q` — would have order `3`
  have ha2ne : (C₁ • (E⁄ℚ)).a₂ ≠ 0 := by
    intro hz
    have h3P : Point.some 0 0 h00' + Point.some 0 0 h00' + Point.some 0 0 h00' = 0 :=
      MazurLevel18.order_three_of_a₂_eq_zero hz hE1a₄ (by rw [hE1a₃]; exact ha3ne) h00'
    have hQ3 : Q + Q + Q = 0 := by
      have hc := congrArg (Point.equivVariableChange (E⁄ℚ) C₁) h3P
      rwa [map_add, map_add, map_zero, hmap] at hc
    have hd : addOrderOf Q ∣ 3 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by
        have e : (3 : ℕ) • Q = Q + Q + Q := by abel
        rw [e]; exact hQ3)
    rw [hQ] at hd; norm_num at hd
  -- the scaling that equalises `a₂` and `a₃`
  set u : ℚˣ := Units.mk0 ((C₁ • (E⁄ℚ)).a₃ / (C₁ • (E⁄ℚ)).a₂)
    (div_ne_zero (by rw [hE1a₃]; exact ha3ne) ha2ne)
  set C₂ : VariableChange ℚ := ⟨u, 0, 0, 0⟩ with hC₂
  have huv : (u : ℚ) = (C₁ • (E⁄ℚ)).a₃ / (C₁ • (E⁄ℚ)).a₂ := rfl
  have hune : (u : ℚ) ≠ 0 := u.ne_zero
  set b : ℚ := -(C₂ • (C₁ • (E⁄ℚ))).a₂ with hbdef
  set c : ℚ := 1 - (C₂ • (C₁ • (E⁄ℚ))).a₁ with hcdef
  have hA4 : (C₂ • (C₁ • (E⁄ℚ))).a₄ = 0 := by
    rw [WeierstrassCurve.variableChange_a₄, hC₂]; simp [hE1a₄]
  have hA6 : (C₂ • (C₁ • (E⁄ℚ))).a₆ = 0 := by
    rw [WeierstrassCurve.variableChange_a₆, hC₂]; simp [hE1a₆]
  have hA23 : (C₂ • (C₁ • (E⁄ℚ))).a₃ = (C₂ • (C₁ • (E⁄ℚ))).a₂ := by
    rw [WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₂, hC₂]
    simp only [Units.val_inv_eq_inv_val]
    field_simp [huv]
    rw [huv]; field_simp
    ring
  have hA2v : (C₂ • (C₁ • (E⁄ℚ))).a₂ = ((u : ℚ))⁻¹ ^ 2 * (C₁ • (E⁄ℚ)).a₂ := by
    rw [WeierstrassCurve.variableChange_a₂, hC₂]; simp
  have hA2ne : (C₂ • (C₁ • (E⁄ℚ))).a₂ ≠ 0 := by
    rw [hA2v]; exact mul_ne_zero (pow_ne_zero 2 (inv_ne_zero hune)) ha2ne
  have hbne : b ≠ 0 := by rw [hbdef, neg_ne_zero]; exact hA2ne
  have hEq : C₂ • (C₁ • (E⁄ℚ)) = (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve ℚ) := by
    ext <;> simp [hbdef, hcdef, hA4, hA6, hA23]
  have h00'' : (C₂ • (C₁ • (E⁄ℚ))).toAffine.Nonsingular 0 0 :=
    Affine.nonsingular_zero.mpr ⟨hA6, Or.inl (by rw [hA23]; exact hA2ne)⟩
  have hΔE : (E⁄ℚ).Δ ≠ 0 := (WeierstrassCurve.isUnit_Δ (W := (E⁄ℚ))).ne_zero
  have hΔ2 : (C₂ • (C₁ • (E⁄ℚ))).Δ ≠ 0 := by
    rw [WeierstrassCurve.variableChange_Δ, WeierstrassCurve.variableChange_Δ]
    exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero _))
      (mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) hΔE)
  -- the `j`-invariant is carried along by the two changes of variables
  haveI hellW : (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve ℚ).IsElliptic :=
    hEq ▸ (inferInstance : (C₂ • (C₁ • (E⁄ℚ))).IsElliptic)
  have hjW : E.j = (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve ℚ).j :=
    MazurLevel27.jInvariant_of_variableChange E C₁ C₂ b c hEq
  have hjmul : E.j * (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve ℚ).Δ
      = (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve ℚ).c₄ ^ 3 := by
    rw [hjW]; exact MazurLevel27.cFour_cube_eq _
  refine ⟨b, c, hbne, hEq ▸ hΔ2, hEq ▸ h00'',
    (Point.equivVariableChange (E⁄ℚ) C₁).symm.trans
      ((Point.equivVariableChange (C₁ • (E⁄ℚ)) C₂).symm.trans (Point.equivOfEq hEq)), ?_, hjmul⟩
  have e1 : (Point.equivVariableChange (E⁄ℚ) C₁).symm Q = Point.some 0 0 h00' := by
    rw [← hmap]; exact (Point.equivVariableChange (E⁄ℚ) C₁).symm_apply_apply _
  have e2 : (Point.equivVariableChange (C₁ • (E⁄ℚ)) C₂) (Point.some 0 0 h00'')
      = Point.some 0 0 h00' := by
    rw [Point.equivVariableChange_some]
    exact Point.some_eq_some _ (by simp [hC₂]) (by simp [hC₂])
  simp only [AddEquiv.trans_apply, e1, ← e2, AddEquiv.symm_apply_apply, Point.equivOfEq_some]

/-- **No rational point of order `27` on a curve of `j`-invariant
`−12288000`** (PROVEN 2026-07-25 — the CM torsion content, over the
`X_1(9)` line rather than Olson's tables): the
second half of the level-`27` decomposition.

Curves with `j = −12288000` are exactly the quadratic twists of one
another (`j ≠ 0, 1728`), and they have complex multiplication by the
order of discriminant `−27` in `ℚ(√−3)`. By Olson, "Torsion points on
elliptic curves with given `j`-invariant" (Manuscripta Math. 16, 1975),
the torsion subgroup of a CM elliptic curve over `ℚ` is one of `ℤ/1`,
`ℤ/2`, `ℤ/3`, `ℤ/4`, `ℤ/6`, `(ℤ/2)²` — so it never contains a point of
order `9`, let alone `27`.

Verified with PARI/GP (2026-07-25, statement check only): over the
squarefree twists `y² = x³ − 2430 d² x + (184437/4) d³` with
`|d| ≤ 80`, the torsion subgroup is always trivial or `ℤ/3`; no twist
has a point of order `9`.

Unlike the `X_1(27)` citation it replaces, this node is a statement
about a single explicit twist family and is elementary in Olson's
sense (reduction at the primes of good reduction, using that the CM
field is not contained in `ℚ`).

PROVEN 2026-07-25, and NOT along Olson's route — no reduction theory,
no CM theory and no twist family are used. A point `Q` of order `27`
supplies the point `3 • Q` of order `9`, and a rational point of order
`9` puts the curve on the Kubert line `c = d²(d − 1)`,
`b = c(d² − d + 1)` of the Tate normal form, which is `X_1(9)` — a
genus-`0` modular curve, so the `j`-invariant becomes an explicit
degree-`36` rational function of the parameter `d`. The hypothesis
`j = −12288000` is then the single Diophantine equation
`c₄(d)³ + 12288000 Δ(d) = 0`, and `MazurLevel27.jEquation_rat` shows it
has no rational root — by a four-case congruence modulo `2` on the
homogenised form. So the statement is in fact strengthened for free:
NO curve of `j`-invariant `−12288000` has a rational point of order
`9`, which is the level-`9` half of Olson's table for this
discriminant. The transport of the `j`-invariant into Tate coordinates
is `exists_tateNormalForm_jInvariant_of_order_nine`. -/
theorem WeierstrassCurve.no_torsion_order_27_of_j (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (hj : E.j = -12288000) (Q : (E⁄ℚ).Point) :
    addOrderOf Q ≠ 27 := by
  intro hQ
  haveI : (E⁄ℚ).IsElliptic := inferInstanceAs (E.map (algebraMap ℚ ℚ)).IsElliptic
  have hR : addOrderOf ((3 : ℕ) • Q) = 9 := by
    rw [addOrderOf_nsmul' Q (by decide), hQ]; decide
  obtain ⟨b, c, hb, _hΔ, h00, Ψ, hΨ, hjmul⟩ :=
    E.exists_tateNormalForm_jInvariant_of_order_nine ((3 : ℕ) • Q) hR
  set W : WeierstrassCurve.Affine ℚ := (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve ℚ).toAffine
  have h1 : W.a₁ = 1 - c := rfl
  have h2 : W.a₂ = -b := rfl
  have h3 : W.a₃ = -b := rfl
  have h4 : W.a₄ = 0 := rfl
  -- the order-`9` condition at `(0,0)`, i.e. `ψ₃(c) = 0`
  have hQ9 : (9 : ℕ) • ((3 : ℕ) • Q) = 0 := by rw [← hR]; exact addOrderOf_nsmul_eq_zero _
  have h9 : (9 : ℕ) • (Affine.Point.some 0 0 h00 : W.Point) = 0 := by
    rw [← hΨ, ← map_nsmul, hQ9, map_zero]
  have hpsi := MazurLevel18.psi3_eq_zero h1 h2 h3 h4 hb h00 h9
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hb (pow_eq_zero_iff (n := 3) (by norm_num) |>.mp (by linear_combination -hpsi))
  obtain ⟨d, hcd, hbd⟩ := MazurLevel18.exists_param hc0 hpsi
  refine MazurLevel27.no_jInvariant_of_order_nine b c d hcd hbd ?_
  rw [hj] at hjmul
  linear_combination -hjmul

/-- **No rational point of order `27`** (PROVEN 2026-07-25 from the two
`X_0(27)`-level nodes above, via the bridge
`exists_stable_cyclic_subgroup_of_rational_point`): a rational point of
order `27` gives a `Gal(ℚ̄/ℚ)`-stable cyclic subgroup of order `27` of
the geometric points, hence a non-cuspidal rational point of `X_0(27)`,
which pins `j(E) = −12288000`; and no curve of that `j`-invariant has a
rational point of order `27`.

This replaces the former direct citation of `X_1(27)` (genus `13`,
Mazur 1977, Thm 8) by two shallower nodes; see their docstrings. -/
theorem WeierstrassCurve.no_torsion_order_27 (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (Q : (E⁄ℚ).Point) : addOrderOf Q ≠ 27 := by
  intro hQ
  obtain ⟨g, hgord, hstable⟩ :=
    E.exists_stable_cyclic_subgroup_of_rational_point Q hQ
  exact E.no_torsion_order_27_of_j
    (E.j_of_stable_cyclic_subgroup_order_27 g hgord hstable) Q hQ

/-- **No rational point of order `35`** (PROVEN 2026-07-25 along the
route recorded for this level, from the `X_0` node
`mem_cyclicIsogenyDegrees`): an order-`35` point generates a rational,
hence Galois-stable, cyclic subgroup of order `35`, i.e. a rational
cyclic `35`-isogeny; but `35` is not a cyclic isogeny degree over `ℚ`
(Kenku's list `{1, …, 19, 21, 25, 27, 37, 43, 67, 163}`), so `X_0(35)`
— a curve of genus `3` — already has no non-cuspidal rational point.
The finer statement that `X_1(35)` (genus `25`) has no non-cuspidal
rational point is therefore not needed here. Subsumed in Mazur 1977,
Thm 8. -/
theorem WeierstrassCurve.no_torsion_order_35 (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (Q : (E⁄ℚ).Point) : addOrderOf Q ≠ 35 := by
  intro hQ
  have h := E.mem_cyclicIsogenyDegrees_of_addOrderOf Q (by norm_num) hQ
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  omega

/-- **No rational point of order `49`** (PROVEN 2026-07-25 along the
route this node's own docstring already recorded, from the `X_0` node
`mem_cyclicIsogenyDegrees`): an order-`49` point generates a rational,
hence Galois-stable, cyclic subgroup of order `49`, i.e. a rational
cyclic `49`-isogeny; but `49` is absent from Kenku's list of cyclic
isogeny degrees over `ℚ`, so `X_0(49)` — a curve of genus `1` — already
has no non-cuspidal rational point. The finer statement that `X_1(49)`
(genus `69`) has no non-cuspidal rational point is therefore not needed
here. Subsumed in Mazur 1977, Thm 8. -/
theorem WeierstrassCurve.no_torsion_order_49 (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (Q : (E⁄ℚ).Point) : addOrderOf Q ≠ 49 := by
  intro hQ
  have h := E.mem_cyclicIsogenyDegrees_of_addOrderOf Q (by norm_num) hQ
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  omega

/-- **No rational torsion point of the critical composite orders**
(PROVEN 2026-07-25 — the eleven-way case split over the `Finset`
hypothesis, dispatching to the eleven per-level nodes above): no
elliptic curve over `ℚ` has a rational point of order `n` for
`n ∈ {14, 15, 16, 18, 20, 21, 24, 25, 27, 35, 49}` — the composite
values that are minimal outside Mazur's list `{1, …, 10, 12}` (every
proper divisor is in the list) and have all prime factors `≤ 7`. -/
theorem WeierstrassCurve.no_composite_torsion_order (E : WeierstrassCurve ℚ)
    [E.IsElliptic] {n : ℕ}
    (hn : n ∈ ({14, 15, 16, 18, 20, 21, 24, 25, 27, 35, 49} : Finset ℕ))
    (Q : (E⁄ℚ).Point) : addOrderOf Q ≠ n := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [E.no_torsion_order_14 Q, E.no_torsion_order_15 Q,
    E.no_torsion_order_16 Q, E.no_torsion_order_18 Q,
    E.no_torsion_order_20 Q, E.no_torsion_order_21 Q,
    E.no_torsion_order_24 Q, E.no_torsion_order_25 Q,
    E.no_torsion_order_27 Q, E.no_torsion_order_35 Q,
    E.no_torsion_order_49 Q]

set_option maxRecDepth 8000 in
/-- **The divisor-closure reduction behind Mazur's uniform bound**
(PROVEN — pure natural-number arithmetic): if a positive `n` is
divisible by no prime `≥ 11` and by none of the critical composite
orders `{14, 15, 16, 18, 20, 21, 24, 25, 27, 35, 49}`, then
`n ∈ {1, …, 10, 12}`. The prime-power exclusions `16 = 2⁴`,
`27 = 3³`, `25 = 5²`, `49 = 7²` bound the `2`-, `3`-, `5`-, `7`-adic
valuations, so `n ∣ 2520 = 2³·3²·5·7`; a decidable sweep over the
divisors of `2520` finishes with the remaining composite exclusions. -/
lemma MazurPointOrder.mem_of_no_forbidden_divisor {n : ℕ} (hn : 0 < n)
    (h1 : ∀ ℓ : ℕ, ℓ.Prime → 11 ≤ ℓ → ¬ ℓ ∣ n)
    (h2 : ∀ d ∈ ({14, 15, 16, 18, 20, 21, 24, 25, 27, 35, 49} : Finset ℕ), ¬ d ∣ n) :
    n ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12} : Finset ℕ) := by
  have h16 : ¬ (2 : ℕ) ^ 4 ∣ n := by have := h2 16 (by decide); simpa using this
  have h27 : ¬ (3 : ℕ) ^ 3 ∣ n := by have := h2 27 (by decide); simpa using this
  have h25 : ¬ (5 : ℕ) ^ 2 ∣ n := by have := h2 25 (by decide); simpa using this
  have h49 : ¬ (7 : ℕ) ^ 2 ∣ n := by have := h2 49 (by decide); simpa using this
  -- the four valuation bounds give `n ∣ 2520`
  have key : ∀ p : ℕ, n.factorization p ≤ (2520 : ℕ).factorization p := by
    intro p
    by_cases hp : p.Prime
    · by_cases hpn : p ∣ n
      · have hple : p ≤ 10 := by
          by_contra h10
          exact h1 p hp (by omega) hpn
        have hp2 : 2 ≤ p := hp.two_le
        interval_cases p
        · have hv : n.factorization 2 ≤ 3 := by
            by_contra hv'
            exact h16 ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
              hn.ne').mpr (by omega))
          exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
            (by norm_num)).mp ((pow_dvd_pow 2 hv).trans (by norm_num))
        · have hv : n.factorization 3 ≤ 2 := by
            by_contra hv'
            exact h27 ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
              hn.ne').mpr (by omega))
          exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
            (by norm_num)).mp ((pow_dvd_pow 3 hv).trans (by norm_num))
        · exact absurd hp (by decide)
        · have hv : n.factorization 5 ≤ 1 := by
            by_contra hv'
            exact h25 ((Nat.Prime.pow_dvd_iff_le_factorization (by decide)
              hn.ne').mpr (by omega))
          exact (Nat.Prime.pow_dvd_iff_le_factorization (by decide)
            (by norm_num)).mp ((pow_dvd_pow 5 hv).trans (by norm_num))
        · exact absurd hp (by decide)
        · have hv : n.factorization 7 ≤ 1 := by
            by_contra hv'
            exact h49 ((Nat.Prime.pow_dvd_iff_le_factorization (by decide)
              hn.ne').mpr (by omega))
          exact (Nat.Prime.pow_dvd_iff_le_factorization (by decide)
            (by norm_num)).mp ((pow_dvd_pow 7 hv).trans (by norm_num))
        · exact absurd hp (by decide)
        · exact absurd hp (by decide)
        · exact absurd hp (by decide)
      · simp [Nat.factorization_eq_zero_of_not_dvd hpn]
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  have hdvd : n ∣ 2520 := by
    rw [← Nat.factorization_le_iff_dvd hn.ne' (by norm_num)]
    exact Finsupp.le_def.mpr key
  have hmem : n ∈ Nat.divisors 2520 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  -- decidable sweep over the divisors of `2520`
  have hforall : ∀ m ∈ Nat.divisors 2520,
      ¬ 14 ∣ m → ¬ 15 ∣ m → ¬ 18 ∣ m → ¬ 20 ∣ m → ¬ 21 ∣ m → ¬ 24 ∣ m → ¬ 35 ∣ m →
      m ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12} : Finset ℕ) := by decide
  exact hforall n hmem (h2 14 (by decide)) (h2 15 (by decide)) (h2 18 (by decide))
    (h2 20 (by decide)) (h2 21 (by decide)) (h2 24 (by decide)) (h2 35 (by decide))

/-- **Mazur's uniform bound on orders of rational torsion points**
(DERIVED 2026-07-23 from the prime leaf `no_prime_torsion_ge_eleven`,
the composite leaf `no_composite_torsion_order`, and the PROVEN
divisor-closure reduction `MazurPointOrder.mem_of_no_forbidden_divisor`):
a rational torsion point of an elliptic curve over `ℚ` has order in
`{1, …, 10, 12}`. Every divisor `d` of the order is realized as the
exact order of a multiple of `Q`, so the two leaves forbid all
divisors outside the reduction's allowed set. Mazur, "Modular curves
and the Eisenstein ideal" (Publ. Math. IHÉS 47, 1977), Thm 8. -/
theorem WeierstrassCurve.mazur_point_order (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) (hQ : Q ∈ Submodule.torsion ℤ (E⁄ℚ).Point) :
    addOrderOf Q ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12} : Finset ℕ) := by
  have hfin : IsOfFinAddOrder Q := by
    rw [← AddCommGroup.mem_torsion, ← Submodule.torsion_int,
      Submodule.mem_toAddSubgroup]
    exact hQ
  have hn0 : addOrderOf Q ≠ 0 := hfin.addOrderOf_pos.ne'
  -- every divisor of the order is the exact order of a multiple of `Q`
  have hdivord : ∀ d : ℕ, d ∣ addOrderOf Q →
      addOrderOf ((addOrderOf Q / d) • Q) = d := fun d hd =>
    addOrderOf_nsmul_addOrderOf_sub hn0 hd
  have h1 : ∀ ℓ : ℕ, ℓ.Prime → 11 ≤ ℓ → ¬ ℓ ∣ addOrderOf Q := fun ℓ hℓ h11 hdvd =>
    E.no_prime_torsion_ge_eleven hℓ h11 _ (hdivord ℓ hdvd)
  have h2 : ∀ d ∈ ({14, 15, 16, 18, 20, 21, 24, 25, 27, 35, 49} : Finset ℕ),
      ¬ d ∣ addOrderOf Q := fun d hd hdvd =>
    E.no_composite_torsion_order hd _ (hdivord d hdvd)
  exact MazurPointOrder.mem_of_no_forbidden_divisor
    (Nat.pos_of_ne_zero hn0) h1 h2

set_option backward.isDefEq.respectTransparency false in
/-- **Finiteness of the rational torsion subgroup** (DERIVED 2026-07-22
from the `mazur_point_order` leaf): the torsion subgroup of `E(ℚ)` is
finite. Every rational torsion point has order in `{1, …, 10, 12}` by
Mazur's uniform bound, hence is killed by `2520 = lcm(1, …, 10, 12)`;
the rational torsion therefore base-changes injectively into the
geometric `2520`-torsion, which has exactly `2520²` elements
(`TorsionCard.card_torsionBy`). The classical standalone routes
(Lutz–Nagell, injectivity of reduction at a good prime) are not needed
once the uniform bound is taken as the leaf. -/
theorem WeierstrassCurve.torsion_finite_rat (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Finite (Submodule.torsion ℤ (E⁄ℚ).Point) := by
  classical
  have hcard : Nat.card
      ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion 2520) = 2520 ^ 2 :=
    TorsionCard.card_torsionBy (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) 2520
      (by norm_num)
  haveI hfin : Finite ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion 2520) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  let ψ : (E⁄ℚ).Point →+ (E⁄(AlgebraicClosure ℚ)).Point :=
    Affine.Point.map (W' := E) (Algebra.ofId ℚ (AlgebraicClosure ℚ))
  let f : Submodule.torsion ℤ (E⁄ℚ).Point →
      (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion 2520 := fun Q =>
    ⟨show ((E.map (algebraMap ℚ (AlgebraicClosure ℚ)))⁄(AlgebraicClosure ℚ)).Point from
      ψ Q.1, by
        rw [Submodule.mem_torsionBy_iff]
        have h2520 : (2520 : ℕ) • (Q.1 : (E⁄ℚ).Point) = 0 := by
          have horder := E.mazur_point_order Q.1 Q.2
          simp only [Finset.mem_insert, Finset.mem_singleton] at horder
          have hdvd : addOrderOf (Q.1 : (E⁄ℚ).Point) ∣ 2520 := by
            rcases horder with h | h | h | h | h | h | h | h | h | h | h <;>
              rw [h] <;> norm_num
          exact addOrderOf_dvd_iff_nsmul_eq_zero.mp hdvd
        show ((2520 : ℕ) : ℤ) • (ψ Q.1) = 0
        rw [natCast_zsmul, ← map_nsmul, h2520, map_zero]⟩
  have hfinj : Function.Injective f := by
    intro Q Q' hQQ
    have h1 : ψ Q.1 = ψ Q'.1 := congrArg Subtype.val hQQ
    exact Subtype.ext (Affine.Point.map_injective (W' := E)
      (f := Algebra.ofId ℚ (AlgebraicClosure ℚ)) h1)
  exact Finite.of_injective f hfinj

/-- The standard embedding of `ℤ/m` into `ℤ/N` for `0 < m ∣ N ≠ 0`
(sending `1` to `N/m`), packaged as an existential (PROVEN): used to
push a full level-`n` structure down to full level-`ℓ` structures at
the prime(-power) divisors `ℓ` of `n`, and to inject cyclic pieces of a
finite abelian group into the factors of its primary decomposition. -/
lemma ZMod.exists_injective_addMonoidHom_of_dvd {m N : ℕ} (hm : 0 < m)
    (hdvd : m ∣ N) (hN : 0 < N) :
    ∃ g : ZMod m →+ ZMod N, Function.Injective g := by
  classical
  obtain ⟨t, rfl⟩ := hdvd
  have ht : 0 < t := Nat.pos_of_ne_zero fun h => by simp [h] at hN
  haveI : NeZero m := ⟨hm.ne'⟩
  haveI : NeZero (m * t) := ⟨hN.ne'⟩
  have hker : (zmultiplesHom (ZMod (m * t))) ((t : ZMod (m * t))) (m : ℤ) = 0 := by
    rw [zmultiplesHom_apply, zsmul_eq_mul]
    push_cast
    rw [← Nat.cast_mul, ZMod.natCast_self]
  refine ⟨ZMod.lift m ⟨(zmultiplesHom (ZMod (m * t))) ((t : ZMod (m * t))), hker⟩, ?_⟩
  intro x y hxy
  -- reduce to the vanishing on the difference
  have hsub : ZMod.lift m ⟨(zmultiplesHom (ZMod (m * t))) ((t : ZMod (m * t))), hker⟩
      (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  set z : ZMod m := x - y
  -- compute the lift on `z` as a natural multiple of `t`
  have hcast : ((((z.val : ℕ) : ℤ) : ZMod m)) = z := by
    push_cast
    exact ZMod.natCast_rightInverse z
  have hgz : ZMod.lift m ⟨(zmultiplesHom (ZMod (m * t))) ((t : ZMod (m * t))), hker⟩
      ((((z.val : ℕ) : ℤ) : ZMod m)) = ((z.val * t : ℕ) : ZMod (m * t)) := by
    rw [ZMod.lift_coe, zmultiplesHom_apply, zsmul_eq_mul]
    push_cast
    ring
  rw [hcast, hsub] at hgz
  have hz0 : ((z.val * t : ℕ) : ZMod (m * t)) = 0 := hgz.symm
  rw [ZMod.natCast_eq_zero_iff] at hz0
  -- cancel `t`: `m ∣ z.val`, so `z.val = 0` by size
  have hdvd' : m ∣ z.val := by
    rcases hz0 with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have h2 : z.val * t = (m * c) * t := by rw [hc]; ring
    exact Nat.eq_of_mul_eq_mul_right ht h2
  have hzero : z.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd' (ZMod.val_lt z)
  have hz : z = 0 := by rw [← hcast, hzero]; simp
  exact sub_eq_zero.mp hz

set_option backward.isDefEq.respectTransparency false in
/-- **Irrationality of full `ℓ`-torsion at an odd prime** (PROVEN
2026-07-22 from the DERIVED determinant node
`det_galoisRep_eq_cyclotomic`): the rational points of an elliptic
curve over `ℚ` contain no subgroup isomorphic to `(ℤ/ℓ)²` for an odd
prime `ℓ`. A rational full level-`ℓ` structure base-changes to all of
the geometric `ℓ`-torsion (both sides have `ℓ²` elements), so the mod-`ℓ`
representation is trivial; its determinant — the mod-`ℓ` cyclotomic
character, by the determinant node — is then trivial, making every
`ℓ`-th root of unity Galois-fixed, hence rational
(`InfiniteGalois.mem_range_algebraMap_iff_fixed`). But a primitive
`ℓ`-th root of unity is not `1`, while `x ↦ x^ℓ` is injective on `ℚ`
for odd `ℓ`. Silverman AEC III.8, Cor 8.1.1. -/
theorem WeierstrassCurve.not_full_odd_prime_torsion_rat (E : WeierstrassCurve ℚ)
    [E.IsElliptic] {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : Odd ℓ)
    (φ : (ZMod ℓ × ZMod ℓ) →+ (E⁄ℚ).Point) :
    ¬ Function.Injective φ := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  intro hφ
  -- the geometric `ℓ`-torsion has `ℓ²` elements
  have hcard : Nat.card
      ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion ℓ) = ℓ ^ 2 :=
    TorsionCard.card_torsionBy (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) ℓ
      (Nat.cast_ne_zero.mpr hℓ.ne_zero)
  haveI hfin : Finite ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion ℓ) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hℓ.ne_zero)
  -- base-change the rational level structure into the geometric torsion
  let ψ : (E⁄ℚ).Point →+ (E⁄(AlgebraicClosure ℚ)).Point :=
    Affine.Point.map (W' := E) (Algebra.ofId ℚ (AlgebraicClosure ℚ))
  have hkill : ∀ z : ZMod ℓ × ZMod ℓ, (ℓ : ℕ) • z = 0 := by
    intro z
    have h1 : ∀ w : ZMod ℓ, (ℓ : ℕ) • w = 0 := fun w => by
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    exact Prod.ext (h1 z.1) (h1 z.2)
  let f : (ZMod ℓ × ZMod ℓ) →
      (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion ℓ := fun z =>
    ⟨show ((E.map (algebraMap ℚ (AlgebraicClosure ℚ)))⁄(AlgebraicClosure ℚ)).Point from
      ψ (φ z), by
        rw [Submodule.mem_torsionBy_iff]
        show ((ℓ : ℕ) : ℤ) • (ψ (φ z)) = 0
        rw [natCast_zsmul, ← map_nsmul, ← map_nsmul, hkill z, map_zero, map_zero]⟩
  have hfinj : Function.Injective f := by
    intro z z' hzz
    exact hφ (Affine.Point.map_injective (W' := E)
      (f := Algebra.ofId ℚ (AlgebraicClosure ℚ)) (congrArg Subtype.val hzz))
  -- by cardinality the level structure exhausts the geometric torsion
  have hfbij : Function.Bijective f :=
    (Nat.bijective_iff_injective_and_card f).mpr
      ⟨hfinj, by rw [hcard, Nat.card_prod, Nat.card_zmod]; ring⟩
  -- so the mod-`ℓ` representation is trivial …
  have hfixall : ∀ (g : Field.absoluteGaloisGroup ℚ)
      (v : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion ℓ),
      E.galoisRep ℓ hℓ.pos g v = v := by
    intro g v
    obtain ⟨z, rfl⟩ := hfbij.surjective v
    refine Subtype.ext ?_
    show Affine.Point.map
        (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom (ψ (φ z)) =
      ψ (φ z)
    show Affine.Point.map
        (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom
        (Affine.Point.map (Algebra.ofId ℚ (AlgebraicClosure ℚ)) (φ z)) =
      Affine.Point.map (Algebra.ofId ℚ (AlgebraicClosure ℚ)) (φ z)
    rw [Affine.Point.map_map]
    have hcomp : ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
          AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ).comp
        (Algebra.ofId ℚ (AlgebraicClosure ℚ)) =
        Algebra.ofId ℚ (AlgebraicClosure ℚ) :=
      AlgHom.ext fun x => by
        simp only [AlgHom.comp_apply, Algebra.ofId_apply]
        exact AlgHom.commutes _ x
    rw [hcomp]
  have hrep1 : ∀ g : Field.absoluteGaloisGroup ℚ, E.galoisRep ℓ hℓ.pos g = 1 := by
    intro g
    apply LinearMap.ext
    intro v
    rw [Module.End.one_apply]
    exact hfixall g v
  -- … its determinant, the mod-`ℓ` cyclotomic character, is trivial …
  have hchar : ∀ g : Field.absoluteGaloisGroup ℚ,
      GaloisRepresentation.cyclotomicCharacterModL ℓ g = 1 := by
    intro g
    have hdet := WeilPairing.det_galoisRep_eq_cyclotomic E ℓ hℓ.pos hodd g
    rw [hrep1 g, Module.End.one_eq_id, LinearMap.det_id] at hdet
    apply Units.ext
    rw [Units.val_one, WeilPairing.cyclotomicCharacterModL_eq_toZMod ℓ g]
    exact hdet.symm
  -- … so every `ℓ`-th root of unity is Galois-fixed, hence rational
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) ℓ
  have hζfix : ∀ σ : Field.absoluteGaloisGroup ℚ, σ ζ = ζ := by
    intro σ
    have h1 := modularCyclotomicCharacter.spec (AlgebraicClosure ℚ)
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) ℓ)
      (MulSemiringAction.toRingAut (Field.absoluteGaloisGroup ℚ)
        (AlgebraicClosure ℚ) σ) hζ.toRootsOfUnity.2
    have h2 : modularCyclotomicCharacter (AlgebraicClosure ℚ)
        (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) ℓ)
        (MulSemiringAction.toRingAut (Field.absoluteGaloisGroup ℚ)
          (AlgebraicClosure ℚ) σ) =
        GaloisRepresentation.cyclotomicCharacterModL ℓ σ := rfl
    rw [h2, hchar σ, Units.val_one, ZMod.val_one, pow_one] at h1
    have h3 : ((hζ.toRootsOfUnity : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
        ζ := hζ.val_toRootsOfUnity_coe
    rw [h3] at h1
    exact h1
  have hrat : ζ ∈ Set.range (algebraMap ℚ (AlgebraicClosure ℚ)) :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed ζ).mpr hζfix
  obtain ⟨q, hq⟩ := hrat
  -- a rational `ℓ`-th root of unity is `1` for odd `ℓ` …
  have hq1 : q ^ ℓ = 1 := by
    have h1 : ζ ^ ℓ = 1 := hζ.pow_eq_one
    rw [← hq, ← map_pow] at h1
    have h2 : algebraMap ℚ (AlgebraicClosure ℚ) (q ^ ℓ) =
        algebraMap ℚ (AlgebraicClosure ℚ) 1 := by rw [map_one]; exact h1
    exact (algebraMap ℚ (AlgebraicClosure ℚ)).injective h2
  have hqone : q = 1 := (hodd.strictMono_pow (R := ℚ)).injective
    (by simpa using hq1)
  -- … contradicting primitivity (`ℓ ≥ 3 > 1`)
  rw [hqone, map_one] at hq
  exact hζ.ne_one hℓ.one_lt hq.symm

/-- **Vieta's formulas for the `2`-division cubic** (PROVEN — pure field
algebra by pairwise root elimination): if `4t³ + Bt² + Ct + D` has three
distinct roots `T`, `U`, `V`, then its coefficients are the scaled
elementary symmetric functions of the roots. Consumed by
`not_full_four_torsion_rat` to identify the `2`-division cubic
`4x³ + b₂x² + 2b₄x + b₆` of a curve with full rational `2`-torsion. -/
lemma MazurFourTorsion.cubic_vieta {B C D T U V : ℚ} (hTU : T ≠ U)
    (hTV : T ≠ V) (hUV : U ≠ V)
    (h1 : 4 * T ^ 3 + B * T ^ 2 + C * T + D = 0)
    (h2 : 4 * U ^ 3 + B * U ^ 2 + C * U + D = 0)
    (h3 : 4 * V ^ 3 + B * V ^ 2 + C * V + D = 0) :
    B = -4 * (T + U + V) ∧ C = 4 * (T * U + T * V + U * V) ∧
      D = -4 * (T * U * V) := by
  have q12 : (T - U) * (4 * (T ^ 2 + T * U + U ^ 2) + B * (T + U) + C) = 0 := by
    linear_combination h1 - h2
  have h12 : 4 * (T ^ 2 + T * U + U ^ 2) + B * (T + U) + C = 0 :=
    (mul_eq_zero.mp q12).resolve_left (sub_ne_zero.mpr hTU)
  have q13 : (T - V) * (4 * (T ^ 2 + T * V + V ^ 2) + B * (T + V) + C) = 0 := by
    linear_combination h1 - h3
  have h13 : 4 * (T ^ 2 + T * V + V ^ 2) + B * (T + V) + C = 0 :=
    (mul_eq_zero.mp q13).resolve_left (sub_ne_zero.mpr hTV)
  have q23 : (U - V) * (4 * (T + U + V) + B) = 0 := by
    linear_combination h12 - h13
  have hB : B = -4 * (T + U + V) := by
    have h0 := (mul_eq_zero.mp q23).resolve_left (sub_ne_zero.mpr hUV)
    linarith
  have hC : C = 4 * (T * U + T * V + U * V) := by
    linear_combination h12 - (T + U) * hB
  have hD : D = -4 * (T * U * V) := by
    linear_combination h1 - T ^ 2 * hB - T * hC
  exact ⟨hB, hC, hD⟩

/-- **The halving square identity** (PROVEN — pure field algebra): if a
point `(x, y)` on a Weierstrass curve doubles, by the tangent-line
formula (`hl` is the cleared slope equation, `hx` the `addX` output),
onto the `2`-torsion abscissa `T`, and `T`, `U`, `V` satisfy the Vieta
identities of the `2`-division cubic (`b₂ = -4σ₁`, `2b₄ = 4σ₂`,
`b₆ = -4σ₃`), then `(T − U)(T − V) = (x − T)²` is a square. This is the
classical identity `x(2P) − e₁ = ((x − e₁)² − (e₁ − e₂)(e₁ − e₃))²/w²`
(`w = 2y + a₁x + a₃`) behind the criterion for halving `2`-torsion
points; the proof is a chain of `linear_combination` certificates
through the completed-square substitution `Y = y + (a₁x + a₃)/2`.
Consumed by `not_full_four_torsion_rat`. -/
lemma MazurFourTorsion.halving_square {a₁ a₂ a₃ a₄ a₆ x y l T U V : ℚ}
    (heq : y ^ 2 + a₁ * x * y + a₃ * y = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
    (hB : a₁ ^ 2 + 4 * a₂ = -4 * (T + U + V))
    (hC : 2 * a₁ * a₃ + 4 * a₄ = 4 * (T * U + T * V + U * V))
    (hD : a₃ ^ 2 + 4 * a₆ = -4 * (T * U * V))
    (hl : l * (2 * y + a₁ * x + a₃) = 3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y)
    (hx : l ^ 2 + a₁ * l - a₂ - x - x = T) :
    (T - U) * (T - V) = (x - T) ^ 2 := by
  -- the `2`-division cubic factors through the three abscissae
  have hw2 : (2 * y + a₁ * x + a₃) ^ 2 = 4 * ((x - T) * (x - U) * (x - V)) := by
    linear_combination 4 * heq + x ^ 2 * hB + x * hC + hD
  -- the completed-square slope `l + a₁/2` clears to the derivative
  have hFp : (l + a₁ / 2) * (2 * y + a₁ * x + a₃) =
      3 * x ^ 2 - 2 * (T + U + V) * x + (T * U + T * V + U * V) := by
    linear_combination hl + x / 2 * hB + (1 : ℚ) / 4 * hC
  -- the doubling output in completed-square form
  have hly : (l + a₁ / 2) ^ 2 = 2 * x + T - (T + U + V) := by
    linear_combination hx + (1 : ℚ) / 4 * hB
  -- the square of the defect vanishes …
  have hN2 : ((x - T) ^ 2 - (T - U) * (T - V)) ^ 2 = 0 := by
    linear_combination
      (-(3 * x ^ 2 - 2 * (T + U + V) * x + (T * U + T * V + U * V)) -
          (l + a₁ / 2) * (2 * y + a₁ * x + a₃)) * hFp +
        (2 * y + a₁ * x + a₃) ^ 2 * hly + (2 * x + T - (T + U + V)) * hw2
  -- … so the defect vanishes
  have hN : (x - T) ^ 2 - (T - U) * (T - V) = 0 := sq_eq_zero_iff.mp hN2
  linarith

/-- **Coordinate extraction for a halved `2`-torsion point** (PROVEN):
if `P + P = T` with `T ≠ 0` of order dividing `2`, then `T` is an affine
point `(θ, u)` on the `2`-torsion locus (`u = negY θ u`), `P` is an
affine point `(x, y)`, and the tangent-line doubling formula lands on
`θ`: the slope `l` satisfies the cleared slope equation and
`l² + a₁l − a₂ − 2x = θ`. Consumed by `not_full_four_torsion_rat`. -/
lemma MazurFourTorsion.exists_halving_coords {W : WeierstrassCurve.Affine ℚ}
    (P T : W.Point) (hPT : P + P = T) (hT2 : T + T = 0) (hT0 : T ≠ 0) :
    ∃ θ u x y l : ℚ,
      (∃ hns : W.Nonsingular θ u, T = Point.some θ u hns) ∧
      W.Equation θ u ∧ u = W.negY θ u ∧ W.Equation x y ∧
      l * (2 * y + W.a₁ * x + W.a₃) =
        3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y ∧
      l ^ 2 + W.a₁ * l - W.a₂ - x - x = θ := by
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, add_zero] at hPT
    exact hT0 hPT.symm
  rcases T with _ | ⟨θ, u, hns⟩
  · exact absurd rfl hT0
  · -- the `2`-torsion condition pins the ordinate: `u = negY θ u`
    have hneg : -Point.some θ u hns = Point.some θ u hns :=
      neg_eq_of_add_eq_zero_left hT2
    rw [Point.neg_some] at hneg
    have hu : W.negY θ u = u := (Point.some.inj hneg).2
    rcases P with _ | ⟨x, y, hPns⟩
    · exact absurd rfl hP0
    · -- `P` is not `2`-torsion (its double `T` is nonzero), so the
      -- tangent-line doubling formula applies
      have hy : y ≠ W.negY x y := fun h =>
        hT0 (hPT.symm.trans (Point.add_self_of_Y_eq h))
      have hadd := Point.add_self_of_Y_ne (h₁ := hPns) hy
      have hθ : W.addX x x (W.slope x x y y) = θ :=
        (Point.some.inj (hadd.symm.trans hPT)).1
      have hsub : y - W.negY x y = 2 * y + W.a₁ * x + W.a₃ := by
        rw [negY]; ring
      have hlm : W.slope x x y y * (2 * y + W.a₁ * x + W.a₃) =
          3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
        rw [← hsub, slope_of_Y_ne rfl hy,
          div_mul_cancel₀ _ (sub_ne_zero.mpr hy)]
      simp only [addX] at hθ
      exact ⟨θ, u, x, y, W.slope x x y y, ⟨hns, rfl⟩, hns.1, hu.symm,
        hPns.1, hlm, hθ⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Irrationality of full `4`-torsion** (PROVEN 2026-07-22 by the
elementary square-product argument): the rational points of an elliptic
curve over `ℚ` contain no subgroup isomorphic to `(ℤ/4)²`. A rational
full level-`4` structure gives three rational points of order `4`
doubling onto the three distinct rational `2`-torsion points
`(θᵢ, uᵢ)`; the θᵢ are then the roots of the `2`-division cubic
`4x³ + b₂x² + 2b₄x + b₆` (`cubic_vieta`), and each halving forces
`(θᵢ − θⱼ)(θᵢ − θₖ)` to be a rational square (`halving_square`). But
the product of the three is `−((θ₁−θ₂)(θ₁−θ₃)(θ₂−θ₃))² < 0`, while a
product of nonzero rational squares is positive — absurd. (The
arithmetic content is `μ₄ ⊄ ℚ`; the Weil-pairing/determinant route
used for odd primes is unavailable here since
`det_galoisRep_eq_cyclotomic` requires `Odd p`.) Silverman AEC III.8,
Cor 8.1.1. -/
theorem WeierstrassCurve.not_full_four_torsion_rat (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (φ : (ZMod 4 × ZMod 4) →+ (E⁄ℚ).Point) :
    ¬ Function.Injective φ := by
  intro hφ
  -- the doubling relations `φ(z) + φ(z) = φ(2z)` for the three order-`4`
  -- elements `(1,0)`, `(0,1)`, `(1,1)` …
  have hdb1 : φ (1, 0) + φ (1, 0) = φ (2, 0) := by
    rw [← map_add]; exact congrArg φ (by decide)
  have hdb2 : φ (0, 1) + φ (0, 1) = φ (0, 2) := by
    rw [← map_add]; exact congrArg φ (by decide)
  have hdb3 : φ (1, 1) + φ (1, 1) = φ (2, 2) := by
    rw [← map_add]; exact congrArg φ (by decide)
  -- … the `2`-torsion relations for their doubles …
  have htor1 : φ (2, 0) + φ (2, 0) = 0 := by
    rw [← map_add, show ((2 : ZMod 4), (0 : ZMod 4)) + (2, 0) = 0 by decide,
      map_zero]
  have htor2 : φ (0, 2) + φ (0, 2) = 0 := by
    rw [← map_add, show ((0 : ZMod 4), (2 : ZMod 4)) + (0, 2) = 0 by decide,
      map_zero]
  have htor3 : φ (2, 2) + φ (2, 2) = 0 := by
    rw [← map_add, show ((2 : ZMod 4), (2 : ZMod 4)) + (2, 2) = 0 by decide,
      map_zero]
  -- … and their nontriviality and pairwise distinctness, by injectivity
  have hne1 : φ (2, 0) ≠ 0 := fun h =>
    absurd (hφ (h.trans (map_zero φ).symm)) (by decide)
  have hne2 : φ (0, 2) ≠ 0 := fun h =>
    absurd (hφ (h.trans (map_zero φ).symm)) (by decide)
  have hne3 : φ (2, 2) ≠ 0 := fun h =>
    absurd (hφ (h.trans (map_zero φ).symm)) (by decide)
  have hne12 : φ (2, 0) ≠ φ (0, 2) := fun h => absurd (hφ h) (by decide)
  have hne13 : φ (2, 0) ≠ φ (2, 2) := fun h => absurd (hφ h) (by decide)
  have hne23 : φ (0, 2) ≠ φ (2, 2) := fun h => absurd (hφ h) (by decide)
  -- extract the affine coordinates of the three halvings
  obtain ⟨θ₁, u₁, x₁, y₁, l₁, ⟨hns₁, hTeq₁⟩, hE₁, hu₁, hP₁, hl₁, hx₁⟩ :=
    MazurFourTorsion.exists_halving_coords _ _ hdb1 htor1 hne1
  obtain ⟨θ₂, u₂, x₂, y₂, l₂, ⟨hns₂, hTeq₂⟩, hE₂, hu₂, hP₂, hl₂, hx₂⟩ :=
    MazurFourTorsion.exists_halving_coords _ _ hdb2 htor2 hne2
  obtain ⟨θ₃, u₃, x₃, y₃, l₃, ⟨hns₃, hTeq₃⟩, hE₃, hu₃, hP₃, hl₃, hx₃⟩ :=
    MazurFourTorsion.exists_halving_coords _ _ hdb3 htor3 hne3
  rw [negY] at hu₁ hu₂ hu₃
  rw [equation_iff] at hE₁ hE₂ hE₃ hP₁ hP₂ hP₃
  -- distinct `2`-torsion points have distinct abscissae (the ordinate
  -- is determined by `2u = -(a₁θ + a₃)`)
  have hd12 : θ₁ ≠ θ₂ := by
    intro h
    subst h
    have huu : u₁ = u₂ := by linarith
    subst huu
    rw [hTeq₁, hTeq₂] at hne12
    exact hne12 rfl
  have hd13 : θ₁ ≠ θ₃ := by
    intro h
    subst h
    have huu : u₁ = u₃ := by linarith
    subst huu
    rw [hTeq₁, hTeq₃] at hne13
    exact hne13 rfl
  have hd23 : θ₂ ≠ θ₃ := by
    intro h
    subst h
    have huu : u₂ = u₃ := by linarith
    subst huu
    rw [hTeq₂, hTeq₃] at hne23
    exact hne23 rfl
  -- the three abscissae are roots of the `2`-division cubic
  have hroot₁ : 4 * θ₁ ^ 3 + ((E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂) * θ₁ ^ 2 +
      (2 * (E⁄ℚ).a₁ * (E⁄ℚ).a₃ + 4 * (E⁄ℚ).a₄) * θ₁ +
      ((E⁄ℚ).a₃ ^ 2 + 4 * (E⁄ℚ).a₆) = 0 := by
    linear_combination (2 * u₁ + (E⁄ℚ).a₁ * θ₁ + (E⁄ℚ).a₃) * hu₁ - 4 * hE₁
  have hroot₂ : 4 * θ₂ ^ 3 + ((E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂) * θ₂ ^ 2 +
      (2 * (E⁄ℚ).a₁ * (E⁄ℚ).a₃ + 4 * (E⁄ℚ).a₄) * θ₂ +
      ((E⁄ℚ).a₃ ^ 2 + 4 * (E⁄ℚ).a₆) = 0 := by
    linear_combination (2 * u₂ + (E⁄ℚ).a₁ * θ₂ + (E⁄ℚ).a₃) * hu₂ - 4 * hE₂
  have hroot₃ : 4 * θ₃ ^ 3 + ((E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂) * θ₃ ^ 2 +
      (2 * (E⁄ℚ).a₁ * (E⁄ℚ).a₃ + 4 * (E⁄ℚ).a₄) * θ₃ +
      ((E⁄ℚ).a₃ ^ 2 + 4 * (E⁄ℚ).a₆) = 0 := by
    linear_combination (2 * u₃ + (E⁄ℚ).a₁ * θ₃ + (E⁄ℚ).a₃) * hu₃ - 4 * hE₃
  obtain ⟨hB, hC, hD⟩ :=
    MazurFourTorsion.cubic_vieta hd12 hd13 hd23 hroot₁ hroot₂ hroot₃
  -- each halving makes `(θᵢ − θⱼ)(θᵢ − θₖ)` a rational square
  have k₁ : (θ₁ - θ₂) * (θ₁ - θ₃) = (x₁ - θ₁) ^ 2 :=
    MazurFourTorsion.halving_square hP₁ hB hC hD hl₁ hx₁
  have hB₂ : (E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂ = -4 * (θ₂ + θ₁ + θ₃) := by
    linear_combination hB
  have hC₂ : 2 * (E⁄ℚ).a₁ * (E⁄ℚ).a₃ + 4 * (E⁄ℚ).a₄ =
      4 * (θ₂ * θ₁ + θ₂ * θ₃ + θ₁ * θ₃) := by
    linear_combination hC
  have hD₂ : (E⁄ℚ).a₃ ^ 2 + 4 * (E⁄ℚ).a₆ = -4 * (θ₂ * θ₁ * θ₃) := by
    linear_combination hD
  have k₂ : (θ₂ - θ₁) * (θ₂ - θ₃) = (x₂ - θ₂) ^ 2 :=
    MazurFourTorsion.halving_square hP₂ hB₂ hC₂ hD₂ hl₂ hx₂
  have hB₃ : (E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂ = -4 * (θ₃ + θ₁ + θ₂) := by
    linear_combination hB
  have hC₃ : 2 * (E⁄ℚ).a₁ * (E⁄ℚ).a₃ + 4 * (E⁄ℚ).a₄ =
      4 * (θ₃ * θ₁ + θ₃ * θ₂ + θ₁ * θ₂) := by
    linear_combination hC
  have hD₃ : (E⁄ℚ).a₃ ^ 2 + 4 * (E⁄ℚ).a₆ = -4 * (θ₃ * θ₁ * θ₂) := by
    linear_combination hD
  have k₃ : (θ₃ - θ₁) * (θ₃ - θ₂) = (x₃ - θ₃) ^ 2 :=
    MazurFourTorsion.halving_square hP₃ hB₃ hC₃ hD₃ hl₃ hx₃
  -- but the product of the three squares is minus a nonzero square
  have hDne : (θ₁ - θ₂) * (θ₁ - θ₃) * (θ₂ - θ₃) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hd12) (sub_ne_zero.mpr hd13))
      (sub_ne_zero.mpr hd23)
  have hprod : ((x₁ - θ₁) * (x₂ - θ₂) * (x₃ - θ₃)) ^ 2 =
      -(((θ₁ - θ₂) * (θ₁ - θ₃) * (θ₂ - θ₃)) ^ 2) := by
    linear_combination (-(x₂ - θ₂) ^ 2 * (x₃ - θ₃) ^ 2) * k₁ -
      ((θ₁ - θ₂) * (θ₁ - θ₃) * (x₃ - θ₃) ^ 2) * k₂ -
      ((θ₁ - θ₂) * (θ₁ - θ₃) * (θ₂ - θ₁) * (θ₂ - θ₃)) * k₃
  have hpos : (0 : ℚ) < ((θ₁ - θ₂) * (θ₁ - θ₃) * (θ₂ - θ₃)) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hDne))
  linarith [sq_nonneg ((x₁ - θ₁) * (x₂ - θ₂) * (x₃ - θ₃)), hprod, hpos]

/-- **Irrationality of full `n`-torsion for `n ≥ 3`** (DERIVED
2026-07-22 from the PROVEN odd-prime case
`not_full_odd_prime_torsion_rat` and the level-`4` leaf
`not_full_four_torsion_rat`): the rational points of an elliptic curve
over `ℚ` contain no subgroup isomorphic to `(ℤ/n)²` for `n ≥ 3`.
Reduction: if an odd prime `ℓ` divides `n`, the `(n/ℓ)`-multiples give
`(ℤ/ℓ)² ↪ (ℤ/n)²`; otherwise `n ≥ 3` is a power of `2`, so `4 ∣ n` and
`(ℤ/4)² ↪ (ℤ/n)²`. Silverman AEC III.8. -/
theorem WeierstrassCurve.not_full_torsion_rat (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {n : ℕ} (hn : 3 ≤ n) (φ : (ZMod n × ZMod n) →+ (E⁄ℚ).Point) :
    ¬ Function.Injective φ := by
  intro hφ
  by_cases hoddfac : ∃ ℓ : ℕ, ℓ.Prime ∧ Odd ℓ ∧ ℓ ∣ n
  · obtain ⟨ℓ, hℓp, hℓodd, hℓdvd⟩ := hoddfac
    obtain ⟨g, hg⟩ := ZMod.exists_injective_addMonoidHom_of_dvd hℓp.pos hℓdvd
      (by omega)
    have hgg : Function.Injective (g.prodMap g) := by
      rw [AddMonoidHom.coe_prodMap]
      exact hg.prodMap hg
    exact E.not_full_odd_prime_torsion_rat hℓp hℓodd (φ.comp (g.prodMap g))
      (hφ.comp hgg)
  · -- `n` is a power of `2`, so `4 ∣ n`
    have h4 : 4 ∣ n := by
      have h2 : ∀ {d : ℕ}, d.Prime → d ∣ n → d = 2 := by
        intro d hd hdvd
        by_contra hne
        exact hoddfac ⟨d, hd, hd.odd_of_ne_two hne, hdvd⟩
      have hpow := Nat.eq_prime_pow_of_unique_prime_dvd
        (n := n) (p := 2) (by omega) h2
      set k := n.primeFactorsList.length
      have hk2 : 2 ≤ k := by
        by_contra hklt
        have hklt' : k < 2 := by omega
        interval_cases k <;> norm_num at hpow <;> omega
      calc (4 : ℕ) = 2 ^ 2 := rfl
        _ ∣ 2 ^ k := pow_dvd_pow 2 hk2
        _ = n := hpow.symm
    obtain ⟨g, hg⟩ := ZMod.exists_injective_addMonoidHom_of_dvd
      (by norm_num) h4 (by omega)
    have hgg : Function.Injective (g.prodMap g) := by
      rw [AddMonoidHom.coe_prodMap]
      exact hg.prodMap hg
    exact E.not_full_four_torsion_rat (φ.comp (g.prodMap g)) (hφ.comp hgg)

/-! ### `X_1(2,10)`: the discriminant route

The `2026-07-25` audit recorded `not_two_torsion_and_five_point` as
IRREDUCIBLE, needing "`X_1(2,10)` as an arithmetic curve plus a rank-`0`
Mordell–Weil computation for its Jacobian". That is superseded: the two
hypotheses can be combined into a single *explicit* rank-`0` elliptic
curve of conductor `20`, in the elementary Diophantine form
`t² = c³ − 11c² − c`, with no modular curve to construct. The cut is:

1. **Order-`5` ⇒ Tate normal form.** A rational point of order `5` puts
   `E` in the Tate form `E(c) : y² + (1 − c)xy − cy = x³ − cx²`, whose
   discriminant is `Δ(E(c)) = c⁵(c² − 11c − 1)`. This is a rational
   change of variables, so `Δ_E` and `Δ(E(c))` differ by `u¹²`
   (`WeierstrassCurve.variableChange_Δ`), a square.
   [`MazurTwoTen.exists_tate_disc_of_order_five`, PROVEN]
2. **Full `2`-torsion ⇒ `Δ_E` is a rational square.** The three
   `2`-torsion abscissae `θ₁, θ₂, θ₃` are the roots of the `2`-division
   cubic, and `Δ = 16((θ₁−θ₂)(θ₁−θ₃)(θ₂−θ₃))²`.
   [`MazurTwoTen.exists_disc_sq_of_full_two_torsion`, PROVEN]
3. Combining, `c(c² − 11c − 1)` is a rational square with `c ≠ 0`, i.e.
   a rational point on `v² = c³ − 11c² − c` with `c ≠ 0`.
   [`MazurTwoTen.no_rational_solution`, PROVEN — the descent it rests
   on is `QuarticDescent.quartic_no_solution`, also PROVEN]

The curve `v² = c³ − 11c² − c` is conductor `20`, Mordell–Weil rank `0`,
torsion `ℤ/2` generated by `(0,0)`; its only affine rational point is
`(0,0)` (PARI/GP `ellrank`/`elltors`/`ellratpoints`, used here only as
an untrusted searcher — the Lean proof is the elementary descent below).
Note this proves *more* than needed: no elliptic curve over `ℚ` with a
rational `5`-torsion point has square discriminant.
-/

/-- **The quartic of the `X_1(2,10)` descent** (PROVEN 2026-07-25 — the
arithmetic heart of `not_two_torsion_and_five_point`): the quartic
`e² = X⁴ − 11X²Y² − Y⁴` has no solution in coprime nonzero integers.
This is the `2`-descent homogeneous space of the conductor-`20` curve
`v² = c³ − 11c² − c`; the statement is equivalent to that curve having
Mordell–Weil rank `0`, so it cannot be settled by a congruence alone
(the quartic has the rational point `(X, Y, e) = (1, 0, 1)`, i.e. it is
the *trivial* coset and is everywhere locally solvable).

The proof is a genuine infinite descent through the Gaussian integers
and lives in `Fermat/FLT/FreyCurve/QuarticDescent.lean`
(`QuarticDescent.quartic_no_solution`); that file's module docstring
carries the full argument. In outline:

* *Parity.* `X` is odd (mod `8`, `X` even forces `e² ≡ 3` or `7`).
* *Sum of two squares.* `B² + (2e)² = 125 X⁴` with `B = 2Y² + 11X²`
  odd and `gcd(B, e) = 1` — a prime dividing both divides `125X⁴`;
  `p ∣ X` forces `p ∣ Y`, and `p = 5` forces `Y² ≡ 2X² (mod 5)`, with
  `2` a nonresidue mod `5`.
* *Gaussian factorisation.* `α = B + 2ei` is coprime to `ᾱ` in `ℤ[i]`,
  and `(2+i)³ = 2 + 11i` has norm `125`, so (after conjugating if
  needed) `α = (2 + 11i) u γ⁴` for a unit `u` and `γ = p + qi` with
  `N γ = |X|` and `gcd(p, q) = 1`. Since `X` is odd, `R = Re γ⁴` is odd
  and `S = Im γ⁴` even, and `B` odd forces `B = ±(11R + 2S)`.
* *Descent.* With `R = X² − 8p²q²` the two signs give
  `Y² = 4pq(p² − 11pq − q²)` and
  `Y² = (q²−p²)(11p² + 4pq − 11q²)`, both of the SAME shape
  `m'n'(m'² − 11m'n' − n'²) = □` that `no_coprime_solution` starts
  from, with `|m'| + |n'| ≤ 2|X| − 2 < X² + Y²` — an infinite descent
  on `|m| + |n|`.

VERIFIED NUMERICALLY beforehand: no solution with `1 ≤ X, Y ≤ 400`
coprime; and `ellratpoints` finds no point of height `≤ 10⁴` on
`v² = c³ − 11c² − c` beyond `(0,0)`. -/
theorem MazurTwoTen.quartic_no_solution {X Y e : ℤ} (hXY : IsCoprime X Y)
    (hX : X ≠ 0) (hY : Y ≠ 0) :
    e ^ 2 ≠ X ^ 4 - 11 * X ^ 2 * Y ^ 2 - Y ^ 4 :=
  QuarticDescent.quartic_no_solution hXY hX hY

/-- **Integral form of the conductor-`20` rank-`0` statement** (PROVEN
2026-07-25 from `quartic_no_solution`): for coprime `m`, `n` with
`m ≠ 0 < n`, the integer `m·n·(m² − 11mn − n²)` is not a perfect square.

The three factors are pairwise coprime (`m² − 11mn − n² ≡ −n² (mod m)`
and `≡ m² (mod n)`), so by `Int.sq_of_isCoprime` each is `±` a square;
`n > 0` makes `n = b²`, and the sign of the product makes `m` and
`k = m² − 11mn − n²` agree in sign, landing on the quartic
`e² = X⁴ − 11X²Y² − Y⁴` with `(X, Y) = (a, b)` or `(b, a)`.

The nondegeneracy `k ≠ 0` is elementary: `k = 0` gives
`(2m − 11n)² = 125n²`, and stripping the three factors of `5` forces
`5 ∣ m` and `5 ∣ n`, contradicting coprimality. -/
theorem MazurTwoTen.no_coprime_solution {m n : ℤ} (hmn : IsCoprime m n) (hm : m ≠ 0)
    (hn : 0 < n) (hsq : IsSquare (m * n * (m ^ 2 - 11 * m * n - n ^ 2))) : False := by
  have hp5 : Nat.Prime 5 := by decide
  set k : ℤ := m ^ 2 - 11 * m * n - n ^ 2 with hkdef
  -- `k ≠ 0`: otherwise `(2m − 11n)² = 125 n²`, forcing `5 ∣ m` and `5 ∣ n`
  have hk0 : k ≠ 0 := by
    intro h
    rw [hkdef] at h
    have hA : (2 * m - 11 * n) ^ 2 = 125 * n ^ 2 := by linear_combination 4 * h
    obtain ⟨A1, hA1⟩ : (5 : ℤ) ∣ (2 * m - 11 * n) :=
      Int.Prime.dvd_pow' (k := 2) hp5 ⟨25 * n ^ 2, by push_cast; linear_combination hA⟩
    have hA1' : A1 ^ 2 = 5 * n ^ 2 := by
      have h25 : (25 : ℤ) * A1 ^ 2 = 25 * (5 * n ^ 2) := by
        linear_combination hA - (2 * m - 11 * n + 5 * A1) * hA1
      linarith
    obtain ⟨A2, hA2⟩ : (5 : ℤ) ∣ A1 :=
      Int.Prime.dvd_pow' (k := 2) hp5 ⟨n ^ 2, by push_cast; linear_combination hA1'⟩
    have hn5 : n ^ 2 = 5 * A2 ^ 2 := by
      have h5 : (5 : ℤ) * n ^ 2 = 5 * (5 * A2 ^ 2) := by
        linear_combination -hA1' + (A1 + 5 * A2) * hA2
      linarith
    have h3 : (5 : ℤ) ∣ n :=
      Int.Prime.dvd_pow' (k := 2) hp5 ⟨A2 ^ 2, by push_cast; linear_combination hn5⟩
    obtain ⟨n1, hn1⟩ := id h3
    have h4 : (5 : ℤ) ∣ m := by
      have h2m : (5 : ℤ) ∣ 2 * m := ⟨A1 + 11 * n1, by linear_combination hA1 + 11 * hn1⟩
      rcases Int.Prime.dvd_mul' hp5 h2m with hcon | hcon
      · exfalso; norm_num at hcon
      · push_cast at hcon; exact hcon
    exact absurd (Int.isUnit_iff.mp (hmn.isUnit_of_dvd' h4 h3)) (by norm_num)
  -- pairwise coprimality of `m`, `n`, `k`
  have hmk : IsCoprime m k := by
    have h := ((hmn.pow_right (n := 2)).neg_right).add_mul_left_right (m - 11 * n)
    have heq : -n ^ 2 + m * (m - 11 * n) = k := by rw [hkdef]; ring
    rwa [heq] at h
  have hnk : IsCoprime n k := by
    have h := (hmn.symm.pow_right (n := 2)).add_mul_left_right (-(11 * m) - n)
    have heq : m ^ 2 + n * (-(11 * m) - n) = k := by rw [hkdef]; ring
    rwa [heq] at h
  obtain ⟨s, hs⟩ := hsq
  -- each of `m`, `n`, `k` is `±` a square (pairwise coprime, product a square)
  obtain ⟨b, hb⟩ : ∃ b : ℤ, n = b ^ 2 ∨ n = -b ^ 2 :=
    Int.sq_of_isCoprime (hmn.symm.mul_right hnk) (c := s) (by linear_combination hs)
  obtain ⟨a, ha⟩ : ∃ a : ℤ, m = a ^ 2 ∨ m = -a ^ 2 :=
    Int.sq_of_isCoprime (hmn.mul_right hmk) (c := s) (by linear_combination hs)
  obtain ⟨e, he⟩ : ∃ e : ℤ, k = e ^ 2 ∨ k = -e ^ 2 :=
    Int.sq_of_isCoprime (hmk.symm.mul_right hnk.symm) (c := s) (by linear_combination hs)
  -- `n > 0` forces the positive branch
  have hbn : n = b ^ 2 := by
    rcases hb with h | h
    · exact h
    · exfalso; linarith [sq_nonneg b]
  have hb0 : b ≠ 0 := by
    intro hb'
    rw [hb'] at hbn
    norm_num at hbn
    omega
  have ha0 : a ≠ 0 := by
    intro ha'
    apply hm
    rcases ha with h | h <;> simp [h, ha']
  -- `m * n * k = s² ≠ 0` is positive, and `n > 0`, so `m * k > 0`
  have hprod : 0 < m * n * k := by
    refine lt_of_le_of_ne ?_ (Ne.symm (mul_ne_zero (mul_ne_zero hm hn.ne') hk0))
    rw [hs]; exact mul_self_nonneg s
  have hmkpos : 0 < m * k := by
    by_contra hcon
    have hcon' : m * k ≤ 0 := not_lt.mp hcon
    have h1 : m * k * n ≤ 0 := mul_nonpos_iff.mpr (Or.inr ⟨hcon', hn.le⟩)
    linarith [hprod, h1]
  -- `a` and `b` are coprime
  have h2ne : (2 : ℕ) ≠ 0 := by norm_num
  have hab : IsCoprime a b := by
    have h1 : IsCoprime (a ^ 2) (b ^ 2) := by
      rcases ha with h | h
      · rw [← h, ← hbn]; exact hmn
      · have h2 : IsCoprime (-(a ^ 2)) (b ^ 2) := by rw [← h, ← hbn]; exact hmn
        simpa using h2.neg_left
    exact ((h1.of_isCoprime_of_dvd_left (dvd_pow_self a h2ne)).symm.of_isCoprime_of_dvd_left
      (dvd_pow_self b h2ne)).symm
  rcases ha with hma | hma <;> rcases he with hke | hke
  · -- `m = a²`, `k = e²`: the quartic at `(X, Y) = (a, b)`
    have hq : e ^ 2 = a ^ 4 - 11 * a ^ 2 * b ^ 2 - b ^ 4 := by
      rw [← hke, hkdef, hma, hbn]; ring
    exact MazurTwoTen.quartic_no_solution hab ha0 hb0 hq
  · exact absurd hmkpos (by rw [hma, hke]; nlinarith [sq_nonneg a, sq_nonneg e])
  · exact absurd hmkpos (by rw [hma, hke]; nlinarith [sq_nonneg a, sq_nonneg e])
  · -- `m = −a²`, `k = −e²`: the quartic at `(X, Y) = (b, a)`
    have hq0 : -e ^ 2 = a ^ 4 + 11 * a ^ 2 * b ^ 2 - b ^ 4 := by
      rw [← hke, hkdef, hma, hbn]; ring
    have hq : e ^ 2 = b ^ 4 - 11 * b ^ 2 * a ^ 2 - a ^ 4 := by linarith [hq0]
    exact MazurTwoTen.quartic_no_solution hab.symm hb0 ha0 hq

/-- **The conductor-`20` curve has no rational point with `c ≠ 0`**
(PROVEN 2026-07-25 from `no_coprime_solution`): `t² = c³ − 11c² − c`
has no rational solution with `c ≠ 0`. Writing `c = m/n` in lowest
terms, `t·n²` is a rational whose square is the integer
`m·n·(m² − 11mn − n²)`, hence (`Rat.isSquare_intCast_iff`) that integer
is a perfect square — which `no_coprime_solution` forbids. -/
theorem MazurTwoTen.no_rational_solution (c t : ℚ) (hc : c ≠ 0) :
    t ^ 2 ≠ c ^ 3 - 11 * c ^ 2 - c := by
  intro h
  have hn : (0 : ℤ) < (c.den : ℤ) := by exact_mod_cast c.den_pos
  have hm : c.num ≠ 0 := Rat.num_ne_zero.mpr hc
  have hmn : IsCoprime c.num ((c.den : ℤ)) :=
    Int.isCoprime_iff_nat_coprime.mpr (by simpa using c.reduced)
  refine MazurTwoTen.no_coprime_solution hmn hm hn ?_
  rw [← Rat.isSquare_intCast_iff]
  refine ⟨t * (c.den : ℚ) ^ 2, ?_⟩
  have hden0 : ((c.den : ℚ)) ≠ 0 := by exact_mod_cast c.den_ne_zero
  have hnum : (c.num : ℚ) = c * (c.den : ℚ) := (div_eq_iff hden0).mp (Rat.num_div_den c)
  push_cast
  rw [hnum]
  linear_combination -((c.den : ℚ)) ^ 4 * h

/-- **Coordinates of a nonzero rational `2`-torsion point** (PROVEN):
a nonzero point `T` with `T + T = 0` is affine, `T = (θ, u)`, lies on
the curve, and has `u = negY θ u` — so `2u = -(a₁θ + a₃)` pins the
ordinate to the abscissa. This is the `2`-torsion half of
`MazurFourTorsion.exists_halving_coords`, without the halving. -/
lemma MazurTwoTen.exists_two_torsion_coords {W : WeierstrassCurve.Affine ℚ}
    (T : W.Point) (hT2 : T + T = 0) (hT0 : T ≠ 0) :
    ∃ θ u : ℚ, (∃ hns : W.Nonsingular θ u, T = Point.some θ u hns) ∧
      W.Equation θ u ∧ u = W.negY θ u := by
  rcases T with _ | ⟨θ, u, hns⟩
  · exact absurd rfl hT0
  · have hneg : -Point.some θ u hns = Point.some θ u hns :=
      neg_eq_of_add_eq_zero_left hT2
    rw [Point.neg_some] at hneg
    have hu : W.negY θ u = u := (Point.some.inj hneg).2
    exact ⟨θ, u, ⟨hns, rfl⟩, hns.1, hu.symm⟩

/-- **Full rational `2`-torsion makes the discriminant a square**
(PROVEN 2026-07-25): if `(ℤ/2)² ↪ E(ℚ)` then `Δ_E = t²` for a rational
`t`. The three nonzero `2`-torsion points have distinct abscissae
`θ₁, θ₂, θ₃` (the ordinate is determined by the abscissa), which are
the three roots of the `2`-division cubic `4x³ + b₂x² + 2b₄x + b₆`;
`MazurFourTorsion.cubic_vieta` turns that into
`b₂ = -4σ₁`, `b₄ = 2σ₂`, `b₆ = -4σ₃`, and then
`Δ = -b₂²b₈ - 8b₄³ - 27b₆² + 9b₂b₄b₆` with `4b₈ = b₂b₆ - b₄²` is
literally `16((θ₁−θ₂)(θ₁−θ₃)(θ₂−θ₃))²`. -/
theorem MazurTwoTen.exists_disc_sq_of_full_two_torsion (E : WeierstrassCurve ℚ)
    (φ₂ : (ZMod 2 × ZMod 2) →+ (E⁄ℚ).Point) (hφ₂ : Function.Injective φ₂) :
    ∃ t : ℚ, E.Δ = t ^ 2 := by
  have htor1 : φ₂ (1, 0) + φ₂ (1, 0) = 0 := by
    rw [← map_add, show ((1 : ZMod 2), (0 : ZMod 2)) + (1, 0) = 0 by decide, map_zero]
  have htor2 : φ₂ (0, 1) + φ₂ (0, 1) = 0 := by
    rw [← map_add, show ((0 : ZMod 2), (1 : ZMod 2)) + (0, 1) = 0 by decide, map_zero]
  have htor3 : φ₂ (1, 1) + φ₂ (1, 1) = 0 := by
    rw [← map_add, show ((1 : ZMod 2), (1 : ZMod 2)) + (1, 1) = 0 by decide, map_zero]
  have hne1 : φ₂ (1, 0) ≠ 0 := fun h =>
    absurd (hφ₂ (h.trans (map_zero φ₂).symm)) (by decide)
  have hne2 : φ₂ (0, 1) ≠ 0 := fun h =>
    absurd (hφ₂ (h.trans (map_zero φ₂).symm)) (by decide)
  have hne3 : φ₂ (1, 1) ≠ 0 := fun h =>
    absurd (hφ₂ (h.trans (map_zero φ₂).symm)) (by decide)
  have hne12 : φ₂ (1, 0) ≠ φ₂ (0, 1) := fun h => absurd (hφ₂ h) (by decide)
  have hne13 : φ₂ (1, 0) ≠ φ₂ (1, 1) := fun h => absurd (hφ₂ h) (by decide)
  have hne23 : φ₂ (0, 1) ≠ φ₂ (1, 1) := fun h => absurd (hφ₂ h) (by decide)
  obtain ⟨θ₁, u₁, ⟨hns₁, hTeq₁⟩, hE₁, hu₁⟩ :=
    MazurTwoTen.exists_two_torsion_coords _ htor1 hne1
  obtain ⟨θ₂, u₂, ⟨hns₂, hTeq₂⟩, hE₂, hu₂⟩ :=
    MazurTwoTen.exists_two_torsion_coords _ htor2 hne2
  obtain ⟨θ₃, u₃, ⟨hns₃, hTeq₃⟩, hE₃, hu₃⟩ :=
    MazurTwoTen.exists_two_torsion_coords _ htor3 hne3
  rw [negY] at hu₁ hu₂ hu₃
  rw [equation_iff] at hE₁ hE₂ hE₃
  -- distinct `2`-torsion points have distinct abscissae
  have hd12 : θ₁ ≠ θ₂ := by
    intro h; subst h
    have huu : u₁ = u₂ := by linarith
    subst huu
    rw [hTeq₁, hTeq₂] at hne12
    exact hne12 rfl
  have hd13 : θ₁ ≠ θ₃ := by
    intro h; subst h
    have huu : u₁ = u₃ := by linarith
    subst huu
    rw [hTeq₁, hTeq₃] at hne13
    exact hne13 rfl
  have hd23 : θ₂ ≠ θ₃ := by
    intro h; subst h
    have huu : u₂ = u₃ := by linarith
    subst huu
    rw [hTeq₂, hTeq₃] at hne23
    exact hne23 rfl
  -- the three abscissae are the roots of the `2`-division cubic
  have hroot₁ : 4 * θ₁ ^ 3 + ((E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂) * θ₁ ^ 2 +
      (2 * (E⁄ℚ).a₁ * (E⁄ℚ).a₃ + 4 * (E⁄ℚ).a₄) * θ₁ +
      ((E⁄ℚ).a₃ ^ 2 + 4 * (E⁄ℚ).a₆) = 0 := by
    linear_combination (2 * u₁ + (E⁄ℚ).a₁ * θ₁ + (E⁄ℚ).a₃) * hu₁ - 4 * hE₁
  have hroot₂ : 4 * θ₂ ^ 3 + ((E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂) * θ₂ ^ 2 +
      (2 * (E⁄ℚ).a₁ * (E⁄ℚ).a₃ + 4 * (E⁄ℚ).a₄) * θ₂ +
      ((E⁄ℚ).a₃ ^ 2 + 4 * (E⁄ℚ).a₆) = 0 := by
    linear_combination (2 * u₂ + (E⁄ℚ).a₁ * θ₂ + (E⁄ℚ).a₃) * hu₂ - 4 * hE₂
  have hroot₃ : 4 * θ₃ ^ 3 + ((E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂) * θ₃ ^ 2 +
      (2 * (E⁄ℚ).a₁ * (E⁄ℚ).a₃ + 4 * (E⁄ℚ).a₄) * θ₃ +
      ((E⁄ℚ).a₃ ^ 2 + 4 * (E⁄ℚ).a₆) = 0 := by
    linear_combination (2 * u₃ + (E⁄ℚ).a₁ * θ₃ + (E⁄ℚ).a₃) * hu₃ - 4 * hE₃
  obtain ⟨hB, hC, hD⟩ :=
    MazurFourTorsion.cubic_vieta hd12 hd13 hd23 hroot₁ hroot₂ hroot₃
  have ha₁ : (E⁄ℚ).a₁ = E.a₁ := by simp [WeierstrassCurve.baseChange]
  have ha₂ : (E⁄ℚ).a₂ = E.a₂ := by simp [WeierstrassCurve.baseChange]
  have ha₃ : (E⁄ℚ).a₃ = E.a₃ := by simp [WeierstrassCurve.baseChange]
  have ha₄ : (E⁄ℚ).a₄ = E.a₄ := by simp [WeierstrassCurve.baseChange]
  have ha₆ : (E⁄ℚ).a₆ = E.a₆ := by simp [WeierstrassCurve.baseChange]
  simp only [ha₁, ha₂, ha₃, ha₄, ha₆] at hB hC hD
  have hb2 : E.b₂ = -4 * (θ₁ + θ₂ + θ₃) := by
    simp only [WeierstrassCurve.b₂]; linarith [hB]
  have hb4 : E.b₄ = 2 * (θ₁ * θ₂ + θ₁ * θ₃ + θ₂ * θ₃) := by
    simp only [WeierstrassCurve.b₄]; linarith [hC]
  have hb6 : E.b₆ = -4 * (θ₁ * θ₂ * θ₃) := by
    simp only [WeierstrassCurve.b₆]; linarith [hD]
  have hb8 : E.b₈ = (E.b₂ * E.b₆ - E.b₄ ^ 2) / 4 := by
    have h := E.b_relation; linarith
  refine ⟨4 * (θ₁ - θ₂) * (θ₁ - θ₃) * (θ₂ - θ₃), ?_⟩
  simp only [WeierstrassCurve.Δ, hb8, hb2, hb4, hb6]
  ring

/-- **Tate normal form together with its scaling factor** (PROVEN
2026-07-25): a curve `W/ℚ` carrying a rational point `P` with
`2P ≠ 0` and `3P ≠ 0` is `ℚ`-isomorphic to `y² + (1−c)xy − by = x³ − bx²`
by an isomorphism taking `P` to `(0,0)`, and the isomorphism scales the
discriminant by an explicit `u¹²`.

This is `WeierstrassCurve.exists_tateNormalForm` /
`WeierstrassCurve.exists_tateNormalForm_of_order_nine` (same three
changes of variables, same licensing of the two divisions by the two
order hypotheses) with ONE extra piece of data: the two sibling nodes
return only the group isomorphism `Ψ`, and an isomorphism of
Mordell–Weil groups says nothing about discriminants. Here the scaling
unit `u = C₂.u` of the third change of variables is carried out of the
proof, so that `WeierstrassCurve.variableChange_Δ`
(`(C • W).Δ = C.u⁻¹ ^ 12 * W.Δ`) is available downstream. The first
change of variables has `u = 1`, so it contributes nothing to the
scaling. -/
theorem MazurTwoTen.exists_tateNormalForm_scaled (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (P : W.toAffine.Point) (hP2 : P + P ≠ 0) (hP3 : P + P + P ≠ 0) :
    ∃ (b c u : ℚ) (_hu : u ≠ 0) (_hb : b ≠ 0)
      (h00 : (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve ℚ).toAffine.Nonsingular 0 0)
      (Ψ : W.toAffine.Point ≃+ (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve ℚ).toAffine.Point),
      Ψ P = Affine.Point.some 0 0 h00 ∧
        u ^ 12 * W.Δ = (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve ℚ).Δ := by
  -- coordinates of `P`
  obtain ⟨X, Y, hns, hPxy⟩ :
      ∃ (X Y : ℚ) (h : W.toAffine.Nonsingular X Y), P = Affine.Point.some X Y h := by
    rcases hcase : P with _ | ⟨X, Y, h⟩
    · exact absurd (by rw [hcase]; simp [← Affine.Point.zero_def]) hP2
    · exact ⟨X, Y, h, rfl⟩
  -- `2P ≠ 0` is exactly nonvanishing of the tangent denominator at `P`
  have hwne : Y ≠ W.toAffine.negY X Y := fun h =>
    hP2 (by rw [hPxy]; exact Affine.Point.add_self_of_Y_eq h)
  have ha3ne : W.a₃ + X * W.a₁ + 2 * Y ≠ 0 := by
    intro h; exact hwne (by rw [Affine.negY]; linarith [h])
  -- the translating/shearing change of variables
  set s₀ : ℚ := (W.a₄ + 2 * X * W.a₂ - Y * W.a₁ + 3 * X ^ 2) / (W.a₃ + X * W.a₁ + 2 * Y)
    with hs₀
  set C₁ : VariableChange ℚ := ⟨1, X, s₀, Y⟩ with hC₁
  have hE1a₃ : (C₁ • W).a₃ = W.a₃ + X * W.a₁ + 2 * Y := by
    rw [WeierstrassCurve.variableChange_a₃, hC₁]; simp
  have hE1a₄ : (C₁ • W).a₄ = 0 := by
    rw [WeierstrassCurve.variableChange_a₄, hC₁]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    rw [hs₀]
    field_simp
    ring
  have hE1a₆ : (C₁ • W).a₆ = 0 := by
    have heq := hns.1
    rw [Affine.equation_iff] at heq
    rw [WeierstrassCurve.variableChange_a₆, hC₁]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    linear_combination -heq
  have h00' : (C₁ • W).toAffine.Nonsingular 0 0 :=
    Affine.nonsingular_zero.mpr ⟨hE1a₆, Or.inl (by rw [hE1a₃]; exact ha3ne)⟩
  have hmap : Point.equivVariableChange W C₁ (Point.some 0 0 h00') = P := by
    rw [Point.equivVariableChange_some, hPxy]
    exact Point.some_eq_some _ (by simp [hC₁]) (by simp [hC₁])
  -- `a₂ ≠ 0` after the shear, else `(0,0)` — hence `P` — would have order dividing `3`
  have ha2ne : (C₁ • W).a₂ ≠ 0 := by
    intro hz
    refine hP3 ?_
    have h3P : Point.some 0 0 h00' + Point.some 0 0 h00' + Point.some 0 0 h00' = 0 :=
      WeierstrassCurve.three_nsmul_origin_eq_zero _ hz hE1a₄
        (by rw [hE1a₃]; exact ha3ne) h00'
    have hc := congrArg (Point.equivVariableChange W C₁) h3P
    rwa [map_add, map_add, map_zero, hmap] at hc
  -- the scaling that equalises `a₂` and `a₃`
  set u : ℚˣ := Units.mk0 ((C₁ • W).a₃ / (C₁ • W).a₂)
    (div_ne_zero (by rw [hE1a₃]; exact ha3ne) ha2ne)
  set C₂ : VariableChange ℚ := ⟨u, 0, 0, 0⟩ with hC₂
  have huv : (u : ℚ) = (C₁ • W).a₃ / (C₁ • W).a₂ := rfl
  have hune : (u : ℚ) ≠ 0 := u.ne_zero
  set b : ℚ := -(C₂ • (C₁ • W)).a₂ with hbdef
  set c : ℚ := 1 - (C₂ • (C₁ • W)).a₁ with hcdef
  have hA4 : (C₂ • (C₁ • W)).a₄ = 0 := by
    rw [WeierstrassCurve.variableChange_a₄, hC₂]; simp [hE1a₄]
  have hA6 : (C₂ • (C₁ • W)).a₆ = 0 := by
    rw [WeierstrassCurve.variableChange_a₆, hC₂]; simp [hE1a₆]
  have hA23 : (C₂ • (C₁ • W)).a₃ = (C₂ • (C₁ • W)).a₂ := by
    rw [WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₂, hC₂]
    simp only [Units.val_inv_eq_inv_val]
    field_simp [huv]
    rw [huv]; field_simp
    ring
  have hA2v : (C₂ • (C₁ • W)).a₂ = ((u : ℚ))⁻¹ ^ 2 * (C₁ • W).a₂ := by
    rw [WeierstrassCurve.variableChange_a₂, hC₂]; simp
  have hA2ne : (C₂ • (C₁ • W)).a₂ ≠ 0 := by
    rw [hA2v]; exact mul_ne_zero (pow_ne_zero 2 (inv_ne_zero hune)) ha2ne
  have hbne : b ≠ 0 := by rw [hbdef, neg_ne_zero]; exact hA2ne
  have hEq : C₂ • (C₁ • W) = (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve ℚ) := by
    ext <;> simp [hbdef, hcdef, hA4, hA6, hA23]
  have h00'' : (C₂ • (C₁ • W)).toAffine.Nonsingular 0 0 :=
    Affine.nonsingular_zero.mpr ⟨hA6, Or.inl (by rw [hA23]; exact hA2ne)⟩
  -- the discriminant scales by `u⁻¹¹²`; the first change of variables has `u = 1`
  have hΔ : ((u : ℚ))⁻¹ ^ 12 * W.Δ = (C₂ • (C₁ • W)).Δ := by
    rw [WeierstrassCurve.variableChange_Δ, WeierstrassCurve.variableChange_Δ, hC₁, hC₂]
    simp
  refine ⟨b, c, ((u : ℚ))⁻¹, inv_ne_zero hune, hbne, hEq ▸ h00'',
    (Point.equivVariableChange W C₁).symm.trans
      ((Point.equivVariableChange (C₁ • W) C₂).symm.trans (Point.equivOfEq hEq)), ?_, ?_⟩
  · have e1 : (Point.equivVariableChange W C₁).symm P = Point.some 0 0 h00' := by
      rw [← hmap]; exact (Point.equivVariableChange W C₁).symm_apply_apply _
    have e2 : (Point.equivVariableChange (C₁ • W) C₂) (Point.some 0 0 h00'')
        = Point.some 0 0 h00' := by
      rw [Point.equivVariableChange_some]
      exact Point.some_eq_some _ (by simp [hC₂]) (by simp [hC₂])
    simp only [AddEquiv.trans_apply, e1, ← e2, AddEquiv.symm_apply_apply, Point.equivOfEq_some]
  · rw [hΔ, hEq]

/-- **The order-`5` condition on the Tate normal form is `b = c`**
(PROVEN 2026-07-25): if the origin of `E(b,c) : y² + (1−c)xy − by =
x³ − bx²` has order exactly `5`, then `b = c`. This is the one step of
the order-`5` normal form that carries arithmetic content, and it is a
three-line group-law computation rather than a division-polynomial one.

On `E(b,c)` the tangent at `(0,0)` is horizontal (`a₄ = 0`, so the slope
is `a₄/a₃ = 0`), which gives `2P = (b, bc)`; the secant through
`(b, bc)` and `(0,0)` has slope `c`, which gives `3P = (c, b − c)`; and
`−2P = (b, 0)`. So `5P = O`, i.e. `3P = −2P`, reads `c = b` on
abscissae. Only the abscissa is needed — the ordinates then agree
automatically, as they must.

The hypothesis `b ≠ 0` is what makes both formulae the generic ones:
`negY 0 0 = b`, so `b ≠ 0` says `(0,0)` is not `2`-torsion (licensing
the doubling), and `b ≠ 0` is also `x(2P) ≠ x(P)` (licensing the secant).
Husemöller, *Elliptic Curves*, ch. 4; Kubert 1976, §2, Table 3, where the
`X_1(5)` relation is recorded as `b = c`. Verified numerically with
PARI/GP (`elladd`/`ellmul` on `E(c,c)` for many `c`). -/
lemma MazurTwoTen.tateNormalForm_b_eq_c_of_order_five (b c : ℚ) (hb : b ≠ 0)
    (h00 : (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve ℚ).toAffine.Nonsingular 0 0)
    (h5 : addOrderOf (Affine.Point.some 0 0 h00 :
      (⟨1 - c, -b, -b, 0, 0⟩ : WeierstrassCurve ℚ).toAffine.Point) = 5) :
    b = c := by
  set V : WeierstrassCurve ℚ := ⟨1 - c, -b, -b, 0, 0⟩ with hV
  set P : V.toAffine.Point := Affine.Point.some 0 0 h00 with hP
  -- the origin is not `2`-torsion: `negY 0 0 = b ≠ 0`
  have hnegY0 : V.toAffine.negY 0 0 = b := by simp [Affine.negY, hV]
  have hy2 : (0 : ℚ) ≠ V.toAffine.negY 0 0 := by
    rw [hnegY0]; exact fun h => hb h.symm
  -- the tangent at the origin is horizontal
  have hslope0 : V.toAffine.slope 0 0 0 0 = 0 := by
    rw [Affine.slope_of_Y_ne rfl hy2]
    simp [hV]
  -- `2P = (b, bc)`
  have hx2 : V.toAffine.addX 0 0 (V.toAffine.slope 0 0 0 0) = b := by
    rw [hslope0]; simp [hV]
  have hy2' : V.toAffine.addY 0 0 0 (V.toAffine.slope 0 0 0 0) = b * c := by
    rw [hslope0]; simp [Affine.addY, Affine.negY, hV]; ring
  have hns2 : V.toAffine.Nonsingular b (b * c) := by
    have hraw := Affine.nonsingular_add h00 h00 (fun hxy => hy2 hxy.right)
    rwa [hx2, hy2'] at hraw
  have h2P : P + P = Affine.Point.some b (b * c) hns2 := by
    rw [hP, Affine.Point.add_self_of_Y_ne hy2]
    exact Affine.Point.some_eq_some V hx2 hy2'
  -- `3P = (c, b − c)`
  have hbne0 : b ≠ (0 : ℚ) := hb
  have hslope1 : V.toAffine.slope b 0 (b * c) 0 = c := by
    rw [Affine.slope_of_X_ne hbne0]
    field_simp
    ring
  have hx3 : V.toAffine.addX b 0 (V.toAffine.slope b 0 (b * c) 0) = c := by
    rw [hslope1]; simp [hV]; ring
  have hy3 : V.toAffine.addY b 0 (b * c) (V.toAffine.slope b 0 (b * c) 0) = b - c := by
    rw [hslope1]; simp [Affine.addY, Affine.negY, hV]; ring
  have hns3 : V.toAffine.Nonsingular c (b - c) := by
    have hraw := Affine.nonsingular_add hns2 h00 (fun hxy => hbne0 hxy.left)
    rwa [hx3, hy3] at hraw
  have h3P : P + P + P = Affine.Point.some c (b - c) hns3 := by
    rw [h2P, hP, Affine.Point.add_of_X_ne hbne0]
    exact Affine.Point.some_eq_some V hx3 hy3
  -- `5P = 0`, i.e. `3P = −2P`, and `−2P = (b, 0)`
  have h5P : (5 : ℕ) • P = 0 := by rw [← h5]; exact addOrderOf_nsmul_eq_zero P
  have hsum : P + P + P + (P + P) = 0 := by rw [← h5P]; abel
  rw [h3P, h2P, add_eq_zero_iff_eq_neg, Affine.Point.neg_some,
    Affine.Point.some.injEq] at hsum
  exact hsum.1.symm

/-- **The discriminant of the diagonal Tate normal form** (PROVEN):
`E(c,c) : y² + (1−c)xy − cy = x³ − cx²` has `b₂ = c² − 6c + 1`,
`b₄ = c² − c`, `b₆ = c²`, `b₈ = −c³`, hence
`Δ = c⁵(c² − 11c − 1)`. This is the plane model of `X_1(5)`:
the `c`-line, with the cusps at `c = 0` and at the roots of
`c² − 11c − 1`. -/
lemma MazurTwoTen.tateNormalForm_Δ_diag (c : ℚ) :
    (⟨1 - c, -c, -c, 0, 0⟩ : WeierstrassCurve ℚ).Δ = c ^ 5 * (c ^ 2 - 11 * c - 1) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- **Tate normal form at a rational point of order `5`** (PROVEN
2026-07-25): if `E/ℚ` carries a rational point of order `5` then, for
some nonzero `c` and `u`, `u¹² Δ_E = c⁵(c² − 11c − 1)`.

This is the classical Tate normal form (Husemöller, *Elliptic Curves*,
§4.4; Knapp §III.1), and every step of it is rational:

1. Translate the order-`5` point to `(0,0)`; this kills `a₆`.
2. The point is not `2`-torsion, so `a₃ ≠ 0`; the shear
   `y ↦ y − (a₄/a₃)x` kills `a₄`, leaving
   `y² + a₁xy + a₃y = x³ + a₂x²`.
3. The point is not `3`-torsion, so `a₂ ≠ 0`; the scaling
   `(x, y) ↦ (u²x, u³y)` with `u = a₃/a₂` makes `a₂ = a₃ =: b`, giving
   Tate's `E(b, c)` with `c := 1 − a₁`.
4. `5P = O` is exactly `b = c` — this is the one step with arithmetic
   content, a group-law computation.

Steps 1–3 are `MazurTwoTen.exists_tateNormalForm_scaled` just above (the
same construction as `WeierstrassCurve.exists_tateNormalForm` and
`WeierstrassCurve.exists_tateNormalForm_of_order_nine`, but returning the
scaling unit as well, which is what makes the discriminant statement
available); step 4 is
`MazurTwoTen.tateNormalForm_b_eq_c_of_order_five`; and
`MazurTwoTen.tateNormalForm_Δ_diag` computes
`Δ(E(c,c)) = c⁵(c² − 11c − 1)`. `c ≠ 0` because `b ≠ 0`, and `b ≠ 0`
because the normal form's `a₂` is a unit multiple of the sheared curve's
`a₂`, which is nonzero because `3P ≠ 0`. The `u¹²` is
`WeierstrassCurve.variableChange_Δ`
(`(C • W).Δ = C.u⁻¹ ^ 12 * W.Δ`).

RESOLVED MACHINERY (the three pieces the earlier note listed as
missing): (a) transport of `WeierstrassCurve.Affine.Point` along a
`VariableChange` is `Affine.Point.equivVariableChange` in this repo's
mathlib shim (`Fermat/FLT/Mathlib/AlgebraicGeometry/EllipticCurve/
Affine/Point.lean`) — mathlib itself still has only `Point.map` along
ring homs, and the reference project `~/cs/FLT` has the identical shim
and no Tate normal form; (b) the normal-form existence statement is now
proven three times over in this file, `exists_tateNormalForm` (order
`≥ 4`), `exists_tateNormalForm_of_order_nine`, and the scaled version
above; (c) the translation of `addOrderOf Q = 5` into `b = c` did NOT
need the `5`-division polynomial — the plain group law suffices, since
`2P` and `3P` on `E(b,c)` have closed-form coordinates. -/
theorem MazurTwoTen.exists_tate_disc_of_order_five (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (Q : (E⁄ℚ).Point) (hQ : addOrderOf Q = 5) :
    ∃ c u : ℚ, u ≠ 0 ∧ c ≠ 0 ∧ u ^ 12 * E.Δ = c ^ 5 * (c ^ 2 - 11 * c - 1) := by
  haveI : (E⁄ℚ).IsElliptic := inferInstanceAs (E.map (algebraMap ℚ ℚ)).IsElliptic
  have hQ2 : Q + Q ≠ 0 := by
    intro h
    have hd : addOrderOf Q ∣ 2 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by rw [two_nsmul]; exact h)
    rw [hQ] at hd; norm_num at hd
  have hQ3 : Q + Q + Q ≠ 0 := by
    intro h
    have hd : addOrderOf Q ∣ 3 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by
        have e : (3 : ℕ) • Q = Q + Q + Q := by abel
        rw [e]; exact h)
    rw [hQ] at hd; norm_num at hd
  obtain ⟨b, c, u, hu, hb, h00, Ψ, hΨ, hΔ⟩ :=
    MazurTwoTen.exists_tateNormalForm_scaled (E⁄ℚ) Q hQ2 hQ3
  have h5 : addOrderOf (Affine.Point.some 0 0 h00) = 5 := by
    rw [← hΨ, AddEquiv.addOrderOf_eq]; exact hQ
  have hbc : b = c := MazurTwoTen.tateNormalForm_b_eq_c_of_order_five b c hb h00 h5
  subst hbc
  refine ⟨b, u, hu, hb, ?_⟩
  have hΔE : (E⁄ℚ).Δ = E.Δ := by simp [WeierstrassCurve.baseChange]
  rw [← hΔE, hΔ, MazurTwoTen.tateNormalForm_Δ_diag]

/-- **No full rational `2`-torsion together with a rational point of
order `5`** (PROVEN 2026-07-25 modulo the single leaf
`MazurTwoTen.quartic_no_solution`; the other input,
`MazurTwoTen.exists_tate_disc_of_order_five`, was closed the same day):
no elliptic curve over `ℚ` has an
injective `(ℤ/2)² →+ E(ℚ)` and a rational point of order `5`
simultaneously. This is the `X_1(2,10)` content — the hypotheses say
exactly that `E(ℚ)` contains `ℤ/2 × ℤ/10` (order `20`), the first
`ℤ/2 × ℤ/2m` beyond Mazur's list (Kenku, "Certain torsion points on
elliptic curves defined over the rationals"; subsumed in Mazur 1977,
Thm 8).

The proof does NOT build `X_1(2,10)` as an arithmetic curve. The
order-`5` point gives a Tate parameter `c ≠ 0` with
`u¹²Δ_E = c⁵(c² − 11c − 1)`, and full `2`-torsion gives `Δ_E = t²`;
so `(u⁶t/c²)² = c³ − 11c² − c`, a rational point with `c ≠ 0` on the
conductor-`20` rank-`0` curve, which `no_rational_solution` forbids.
See the section header above for the full route and the audit of the
earlier "IRREDUCIBLE" verdict that this supersedes. -/
theorem WeierstrassCurve.not_two_torsion_and_five_point (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (φ₂ : (ZMod 2 × ZMod 2) →+ (E⁄ℚ).Point)
    (hφ₂ : Function.Injective φ₂) (Q : (E⁄ℚ).Point) (hQ : addOrderOf Q = 5) :
    False := by
  obtain ⟨t, ht⟩ := MazurTwoTen.exists_disc_sq_of_full_two_torsion E φ₂ hφ₂
  obtain ⟨c, u, hu, hc, hcu⟩ := MazurTwoTen.exists_tate_disc_of_order_five E Q hQ
  refine MazurTwoTen.no_rational_solution c (u ^ 6 * t / c ^ 2) hc ?_
  rw [div_pow, div_eq_iff (pow_ne_zero 2 (pow_ne_zero 2 hc))]
  linear_combination hcu - u ^ 12 * ht

/-- **Exclusion of rational `ℤ/2 × ℤ/10`** (DERIVED 2026-07-23 from
the leaf `not_two_torsion_and_five_point` by splitting off the
`2`- and `5`-primary parts of `ℤ/2 × ℤ/10`): the modular curve
`X_1(2,10)` has no non-cuspidal rational point (Mazur 1977; the list
of fifteen). The subgroup `⟨(1,0), (0,5)⟩` is a full `2`-torsion and
`φ(0,2)` has exact order `5`. -/
theorem WeierstrassCurve.not_two_ten_torsion (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (φ : (ZMod 2 × ZMod 10) →+ (E⁄ℚ).Point) :
    ¬ Function.Injective φ := by
  intro hφ
  -- the `2`-primary embedding `(ℤ/2)² ↪ ℤ/2 × ℤ/10`
  obtain ⟨g, hg⟩ := ZMod.exists_injective_addMonoidHom_of_dvd
    (by norm_num : (0 : ℕ) < 2) (by norm_num : (2 : ℕ) ∣ 10) (by norm_num)
  have hgg : Function.Injective ((AddMonoidHom.id (ZMod 2)).prodMap g) := by
    rw [AddMonoidHom.coe_prodMap]
    exact Function.Injective.prodMap (fun _ _ h => h) hg
  -- the point of order `5`
  have hQ : addOrderOf (φ ((0 : ZMod 2), (2 : ZMod 10))) = 5 := by
    rw [addOrderOf_injective φ hφ]
    haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
    exact addOrderOf_eq_prime (by decide) (by decide)
  exact E.not_two_torsion_and_five_point
    (φ.comp ((AddMonoidHom.id (ZMod 2)).prodMap g)) (hφ.comp hgg) _ hQ

/-! ### `X_1(2,12)`: the `ℤ/2 × ℤ/12` exclusion, cut down to one quartic

The old `IRREDUCIBLE` audit on `not_two_four_torsion_and_three_point`
(2026-07-25) claimed the node needs `X_1(2,12)` as an arithmetic curve.
That was too pessimistic: `X_1(2,12)` admits an ELEMENTARY plane model,
reached from the halving machinery already in this file, and the whole
geometric-to-arithmetic passage is proven below. What was left was
exactly one Diophantine statement over `ℚ` —
`MazurTwoTwelve.quartic_only_trivial`, namely that the genus-`1` quartic
`v² = (j² − 1)(j² + 3)` has no rational point with `v ≠ 0`. That is now
PROVEN too (2026-07-26), by the elementary infinite descent developed in
`MazurTwoTwelve.Quartic` below; the whole `ℤ/2 × ℤ/12` exclusion is
therefore unconditional.

The route (2026-07-25), each step proven below:

1. `ψ` gives full rational `2`-torsion `T = ψ(0,2)`, `U = ψ(1,0)`,
   `V = ψ(1,2)` with `T` halved by `P = ψ(0,1)`. The abscissae `θ_T`,
   `θ_U`, `θ_V` are the roots of the `2`-division cubic (`cubic_vieta`).
2. The halving makes BOTH `θ_T − θ_U` and `θ_T − θ_V` rational squares,
   `m²` and `n²` (`MazurTwoTwelve.halving_squares` — a strengthening of
   `MazurFourTorsion.halving_square`, which only gives the PRODUCT; the
   extra content is the classical identity
   `x(2P) − e₂ = ((x − e₂)² − (e₂ − e₁)(e₂ − e₃))²/(2y + a₁x + a₃)²`).
   This is where the old audit stopped: it is not one square condition
   but two, and together with the order-`3` point they suffice.
3. A rational point `Q` of order `3` is an inflection: `Q + Q = -Q`, so
   its tangent slope `l` satisfies `l² + a₁l − a₂ − 2x = x`
   (`MazurTwoTwelve.exists_order_three_coords`). Writing `μ = l + a₁/2`,
   `w = 2y + a₁x + a₃` and `X = x_Q − θ_T`, the three identities
   `w² = 4X(X + m²)(X + n²)`, `μ² = 3X + m² + n²` and
   `μw = 3X² + 2(m² + n²)X + m²n²` give, by `(μw)² = μ²w²`, the
   `3`-division equation `3X⁴ + 4(m²+n²)X³ + 6m²n²X² − m⁴n⁴ = 0`.
4. `MazurTwoTwelve.no_rational_solution` scales `n` away and solves that
   quadratic in `m²`: its discriminant is `16Z³(Z+1)³`, so `S² = Z² + Z`
   is a rational conic, parametrised by `k` via `4kZ = (k−1)²`,
   `4kS = 1 − k²`. Then `16k³M² = −(k−1)³(3k+1)` and
   `16k³(Z + M²) = (k² − 1)²`, while `Z + M²` is a square because
   `w² = 4Z(Z+1)(Z+M²) = 4S²(Z+M²)`. Hence `k = j²`, and eliminating
   gives `(4jM/(j²−1))² = (J² − 1)(J² + 3)` with `J = 1/j`. The only
   rational points have `4jM = 0`, i.e. `M = 0` — the cusp.

`quartic_only_trivial` is the rank-`0` content: the smooth model of
`v² = j⁴ + 2j² − 3` is the conductor-`24` curve `24a` (`ellfromeqn` gives
`[0,2,0,12,24]`), of Mordell–Weil rank `0` with torsion `ℤ/4`. Its four
rational points are the two at infinity and `(±1, 0)`, so every affine
one has `v = 0`. Equivalently, via `u + 1 = t + 1/t` on `u = j²`, it is
`t(t² − t + 1) = □`, i.e. `Y² = X³ − X² + X` — also conductor `24`,
rank `0`, torsion `ℤ/4` generated by `(1,1)`. The elementary descent:
`X = d²/e²` with `gcd(d,e) = 1` forces `d⁴ − d²e² + e⁴ = f²`, whose only
coprime solutions are `d = 0`, `e = 0` or `d² = e²` (equivalently the
concordant system `g² + h² = □`, `g² + 4h² = □` with `g = d² − e²`,
`h = de`).

The descent actually formalised (2026-07-26) is NOT that one. Splitting
`d⁴ − d²e² + e⁴ = f²` by the parity of `d`, `e`, the both-odd branch does
descend — `h = u² − v²`, `g = ±2uv` gives
`u⁴ − u²v² + v⁴ = ((d²+e²)/2)²` with
`f² − ((d²+e²)/2)² = 3(d²−e²)²/4 > 0` — but the opposite-parity branch
returns `{u,v} = {d,e}` and does not, which is why the literature
parametrises `u² − uv + v² = w²` by Eisenstein triples in `ℤ[ω]`,
machinery mathlib does not have. `MazurTwoTwelve.Quartic` closes that
branch instead by factoring `f² − (e² − 2c₀²)² = 12c₀⁴` over `ℤ`; see the
section comment there.
-/

/-- **Each halving difference is a square** (PROVEN 2026-07-25 — pure
field algebra, strengthening `MazurFourTorsion.halving_square`): under
the hypotheses of `halving_square` (a rational point `(x, y)` doubling
onto the `2`-torsion abscissa `T`, with `T`, `U`, `V` the roots of the
`2`-division cubic and pairwise distinct), BOTH `T − U` and `T − V` are
rational squares, not merely their product.

The extra ingredient over `halving_square` is the classical identity
`x(2P) − e₂ = ((x − e₂)² − (e₂ − e₁)(e₂ − e₃))² / (2y + a₁x + a₃)²`
evaluated at `e₁ = T`: since `x(2P) = T`, this exhibits `T − U` as a
square. The `linear_combination` certificate is `(T − U)·hw₂` plus
`(x² − 2Tx + T(U+V) − UV)` times the `halving_square` conclusion, the
polynomial cofactor of `(x − T)² − (T − U)(T − V)` in
`4(T − U)(x − T)(x − U)(x − V) − ((x − U)² − (U − T)(U − V))²`.

Nonvanishing of `w = 2y + a₁x + a₃` is forced: `w = 0` would put `x` at
one of `T`, `U`, `V`, and each case contradicts the distinctness of the
abscissae through `halving_square`. -/
lemma MazurTwoTwelve.halving_squares {a₁ a₂ a₃ a₄ a₆ x y l T U V : ℚ}
    (heq : y ^ 2 + a₁ * x * y + a₃ * y = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
    (hB : a₁ ^ 2 + 4 * a₂ = -4 * (T + U + V))
    (hC : 2 * a₁ * a₃ + 4 * a₄ = 4 * (T * U + T * V + U * V))
    (hD : a₃ ^ 2 + 4 * a₆ = -4 * (T * U * V))
    (hl : l * (2 * y + a₁ * x + a₃) = 3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y)
    (hx : l ^ 2 + a₁ * l - a₂ - x - x = T)
    (hTU : T ≠ U) (hTV : T ≠ V) (hUV : U ≠ V) :
    ∃ m n : ℚ, T - U = m ^ 2 ∧ T - V = n ^ 2 := by
  have hw2 : (2 * y + a₁ * x + a₃) ^ 2 = 4 * ((x - T) * (x - U) * (x - V)) := by
    linear_combination 4 * heq + x ^ 2 * hB + x * hC + hD
  have hN : (T - U) * (T - V) = (x - T) ^ 2 :=
    MazurFourTorsion.halving_square heq hB hC hD hl hx
  have hw0 : 2 * y + a₁ * x + a₃ ≠ 0 := by
    intro h
    rw [h] at hw2
    have h3 : (x - T) * (x - U) * (x - V) = 0 := by
      linear_combination (-1 / 4 : ℚ) * hw2
    rcases mul_eq_zero.mp h3 with h4 | h4
    · rcases mul_eq_zero.mp h4 with h5 | h5
      · have h6 : (T - U) * (T - V) = 0 := by
          linear_combination hN + (x - T) * h5
        rcases mul_eq_zero.mp h6 with h7 | h7
        · exact hTU (sub_eq_zero.mp h7)
        · exact hTV (sub_eq_zero.mp h7)
      · have h6 : (T - U) * (U - V) = 0 := by
          linear_combination hN + (x + U - 2 * T) * h5
        rcases mul_eq_zero.mp h6 with h7 | h7
        · exact hTU (sub_eq_zero.mp h7)
        · exact hUV (sub_eq_zero.mp h7)
    · have h6 : (T - V) * (V - U) = 0 := by
        linear_combination hN + (x + V - 2 * T) * h4
      rcases mul_eq_zero.mp h6 with h7 | h7
      · exact hTV (sub_eq_zero.mp h7)
      · exact hUV (sub_eq_zero.mp h7).symm
  have hN' : (T - V) * (T - U) = (x - T) ^ 2 := by linear_combination hN
  refine ⟨((x - U) ^ 2 - (U - T) * (U - V)) / (2 * y + a₁ * x + a₃),
    ((x - V) ^ 2 - (V - T) * (V - U)) / (2 * y + a₁ * x + a₃), ?_, ?_⟩
  · rw [div_pow, eq_div_iff (pow_ne_zero 2 hw0)]
    linear_combination (T - U) * hw2 +
      (x ^ 2 - 2 * T * x + T * (U + V) - U * V) * hN
  · rw [div_pow, eq_div_iff (pow_ne_zero 2 hw0)]
    linear_combination (T - V) * hw2 +
      (x ^ 2 - 2 * T * x + T * (V + U) - V * U) * hN'

/-- **Coordinates of a nonzero `2`-torsion point** (PROVEN 2026-07-25):
a nonzero point killed by `2` is affine, and its ordinate is the fixed
point of `negY`. This is the part of
`MazurFourTorsion.exists_halving_coords` that does not need a halving,
extracted so the two UNHALVED `2`-torsion points of a `ℤ/2 × ℤ/4`
structure can be given abscissae as well. -/
lemma MazurTwoTwelve.exists_two_torsion_coords {W : WeierstrassCurve.Affine ℚ}
    (T : W.Point) (hT2 : T + T = 0) (hT0 : T ≠ 0) :
    ∃ θ u : ℚ, (∃ hns : W.Nonsingular θ u, T = Point.some θ u hns) ∧
      W.Equation θ u ∧ u = W.negY θ u := by
  rcases T with _ | ⟨θ, u, hns⟩
  · exact absurd rfl hT0
  · have hneg : -Point.some θ u hns = Point.some θ u hns :=
      neg_eq_of_add_eq_zero_left hT2
    rw [Point.neg_some] at hneg
    have hu : W.negY θ u = u := (Point.some.inj hneg).2
    exact ⟨θ, u, ⟨hns, rfl⟩, hns.1, hu.symm⟩

/-- **Coordinates of a point of order `3`** (PROVEN 2026-07-25): a
rational point of order `3` is an inflection point, `Q + Q = -Q`. It is
affine and not `2`-torsion, so the tangent-line doubling formula applies
and its output abscissa is `x` itself: `l² + a₁l − a₂ − 2x = x`. The
`3`-division polynomial is exactly the resultant of that with the
cleared slope equation, but the inflection form is what the algebra
downstream wants, since it keeps `l` as a rational witness. -/
lemma MazurTwoTwelve.exists_order_three_coords {W : WeierstrassCurve.Affine ℚ}
    (Q : W.Point) (hQ0 : Q ≠ 0) (hQ3 : Q + Q = -Q) :
    ∃ x y l : ℚ, W.Equation x y ∧ 2 * y + W.a₁ * x + W.a₃ ≠ 0 ∧
      l * (2 * y + W.a₁ * x + W.a₃) =
        3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y ∧
      l ^ 2 + W.a₁ * l - W.a₂ - x - x = x := by
  rcases Q with _ | ⟨x, y, hns⟩
  · exact absurd rfl hQ0
  · have hy : y ≠ W.negY x y := by
      intro h
      rw [Point.add_self_of_Y_eq h] at hQ3
      exact hQ0 (neg_eq_zero.mp hQ3.symm)
    have hsub : y - W.negY x y = 2 * y + W.a₁ * x + W.a₃ := by
      rw [negY]; ring
    have hw0 : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
      rw [← hsub]; exact sub_ne_zero.mpr hy
    have hadd := Point.add_self_of_Y_ne (h₁ := hns) hy
    rw [hadd, Point.neg_some] at hQ3
    have hθ : W.addX x x (W.slope x x y y) = x := (Point.some.inj hQ3).1
    have hlm : W.slope x x y y * (2 * y + W.a₁ * x + W.a₃) =
        3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
      rw [← hsub, slope_of_Y_ne rfl hy,
        div_mul_cancel₀ _ (sub_ne_zero.mpr hy)]
    simp only [addX] at hθ
    exact ⟨x, y, W.slope x x y y, hns.1, hw0, hlm, hθ⟩

/-! ### The plane quartic `v² = (j² − 1)(j² + 3)`: an elementary descent

Everything in `MazurTwoTwelve.Quartic` exists to prove
`MazurTwoTwelve.quartic_only_trivial` below.  Mathlib has no arithmetic
of the ring `ℤ[ω]` in the form of an "Eisenstein triple"
parametrisation of `x² − xy + y²  = z²`, which is the standard route;
what is developed here instead is a purely elementary infinite descent
resting only on mathlib's `PythagoreanTriple.coprime_classification'`
and `Int.sq_of_gcd_eq_one`.

The chain is, with `Q(m, n) := m⁴ − m²n² + n⁴`:

* `quartic_int` reduces the rational statement (after clearing
  denominators) to `r² = (p² − q²)(p² + 3q²)`, `gcd(p, q) = 1`, and
  splits it on the parity of `p`, `q`.  Both surviving branches produce
  a *concordant* pair `g² + h² = z²`, `g² + 4h² = w²` with `g` odd.
* `conc_to_quartic` turns such a pair into a solution of
  `z² = Q(m, n)` with `h = mn`, by applying the primitive Pythagorean
  parametrisation to `(g, 2h, w)`.
* `quartic_descent_aux` is the descent on `Q(d, e) = c²` with `d` even,
  `e` odd, `gcd(d, e) = 1`.  Writing `d = 2c₀` gives
  `(f − P)(f + P) = 12c₀⁴` with `f = |c|`, `P = e² − 2c₀²`, both odd, so
  `AB = 3c₀⁴` with `A`, `B` coprime and positive.  Exactly one of them
  carries the `3`, and `fourth_power_split` makes the other pair of
  cofactors fourth powers.
  - The branch `3 ∣ B` gives `e² = 3t⁴ + 2s²t² − s⁴`, impossible mod `8`
    for every parity of `(s, t)` (`case_i_absurd`).  This is the branch
    the classical "both odd / opposite parity" split never reaches, and
    it is what replaces the missing `ℤ[ω]` factorisation.
  - The branch `3 ∣ A` gives `e² = v⁴ + 2u²v² − 3u⁴`, which forces `u`
    even and `v` odd mod `8`, factors as `(v² − u²)(v² + 3u²)` into
    coprime squares `al²`, `be²`, and hence is another concordant pair
    `al² + u² = v²`, `al² + 4u² = be²`.  `quartic_step` feeds it back
    through `conc_to_quartic` to a solution of `v² = Q(m, n)` with
    `u = mn`, and `|v| < 3u⁴ + v⁴ = f`: a strict descent.

The only solutions of `Q(m, n) = c²` with `m`, `n` coprime of opposite
parity therefore have `mn = 0` (`quartic_no_sol`), which is exactly the
rank-`0` content of the conductor-`24` curve `24a`.
-/

namespace MazurTwoTwelve.Quartic

/-! ## Stage 0: congruence helpers -/

lemma odd_sq_emod_eight {x : ℤ} (hx : x % 2 = 1) : x ^ 2 % 8 = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, x = 2 * k + 1 := ⟨x / 2, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j, k * (k + 1) = 2 * j := by
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exact ⟨m * (m + m + 1), by ring⟩
    · exact ⟨(2 * m + 1) * (m + 1), by ring⟩
  have h : (2 * k + 1) ^ 2 = 8 * j + 1 := by linear_combination 4 * hj
  rw [h]; omega

lemma odd_pow_four_emod_eight {x : ℤ} (hx : x % 2 = 1) : x ^ 4 % 8 = 1 := by
  have h2 : x ^ 2 % 2 = 1 := by have := odd_sq_emod_eight hx; omega
  have h3 := odd_sq_emod_eight h2
  have h4 : x ^ 4 = (x ^ 2) ^ 2 := by ring
  rw [h4]; exact h3

lemma even_pow_four_emod_eight {x : ℤ} (hx : x % 2 = 0) : x ^ 4 % 8 = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, x = 2 * k := ⟨x / 2, by omega⟩
  have h : (2 * k) ^ 4 = 8 * (2 * k ^ 4) := by ring
  rw [h]; omega

lemma even_sq_emod_four {x : ℤ} (hx : x % 2 = 0) : x ^ 2 % 4 = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, x = 2 * k := ⟨x / 2, by omega⟩
  have h : (2 * k) ^ 2 = 4 * k ^ 2 := by ring
  rw [h]; omega

lemma mod8_A (E U V W : ℤ) (hE : E % 8 = 1) (h : E = 3 * U + 2 * W - V)
    (hU : U % 8 = 1) (hV : V % 8 = 1) (_hW : W % 8 = 1) : False := by omega

lemma mod8_B (E U V W : ℤ) (hE : E % 8 = 1) (h : E = 3 * U + 2 * W - V)
    (hU : U % 8 = 1) (hV : V % 8 = 0) (hW : W % 4 = 0) : False := by omega

lemma mod8_C (E U V W : ℤ) (hE : E % 8 = 1) (h : E = 3 * U + 2 * W - V)
    (hU : U % 8 = 0) (hV : V % 8 = 1) (hW : W % 4 = 0) : False := by omega

lemma mod8_D (E U V W : ℤ) (hE : E % 8 = 1) (h : E = V + 2 * W - 3 * U)
    (hU : U % 8 = 1) (hV : V % 8 = 1) (_hW : W % 8 = 1) : False := by omega

lemma mod8_E (E U V W : ℤ) (hE : E % 8 = 1) (h : E = V + 2 * W - 3 * U)
    (hU : U % 8 = 1) (hV : V % 8 = 0) (hW : W % 4 = 0) : False := by omega

lemma emod_two_one {a X : ℤ} (h : a = 2 * X + 1) : a % 2 = 1 := by omega

lemma emod_four_zero {a X : ℤ} (h : a = 4 * X) : a % 4 = 0 := by omega

lemma not_emod_eight_one_of_four_dvd {a X : ℤ} (h : a = 4 * X) : a % 8 ≠ 1 := by omega

lemma four_mul_ne {X Y : ℤ} (h : 4 * X = 4 * Y + 1) : False := by omega

/-! ## Stage 1: coprime factorisations -/

lemma sq_of_gcd_of_nonneg {a b c : ℤ} (h : Int.gcd a b = 1) (heq : a * b = c ^ 2)
    (ha : 0 ≤ a) : ∃ a0 : ℤ, a = a0 ^ 2 := by
  obtain ⟨a0, ha0 | ha0⟩ := Int.sq_of_gcd_eq_one h heq
  · exact ⟨a0, ha0⟩
  · rw [ha0] at ha
    have h1 : a0 ^ 2 = 0 := by linarith [sq_nonneg a0]
    exact ⟨0, by rw [ha0, h1]; ring⟩

lemma fourth_power_split {A B c : ℤ} (hA : 0 < A) (hB : 0 < B)
    (hAB : Int.gcd A B = 1) (h : A * B = c ^ 4) :
    ∃ u v : ℤ, A = u ^ 4 ∧ B = v ^ 4 ∧ c ^ 2 = u ^ 2 * v ^ 2 := by
  have h2 : A * B = (c ^ 2) ^ 2 := by rw [h]; ring
  obtain ⟨a0, ha0⟩ := sq_of_gcd_of_nonneg hAB h2 hA.le
  obtain ⟨b0, hb0⟩ :=
    sq_of_gcd_of_nonneg (by rwa [Int.gcd_comm]) (by rw [mul_comm]; exact h2) hB.le
  have hcop : IsCoprime a0 b0 := by
    have h3 : IsCoprime (a0 ^ 2) (b0 ^ 2) := by
      rw [← ha0, ← hb0]; exact Int.isCoprime_iff_gcd_eq_one.mpr hAB
    exact (h3.of_isCoprime_of_dvd_left (dvd_pow_self a0 two_ne_zero)).of_isCoprime_of_dvd_right
      (dvd_pow_self b0 two_ne_zero)
  have habs : |a0| * |b0| = c ^ 2 := by
    have h4 : (|a0| * |b0|) ^ 2 = (c ^ 2) ^ 2 := by
      rw [mul_pow, sq_abs, sq_abs, ← ha0, ← hb0]; exact h2
    have h6 : (|a0| * |b0| - c ^ 2) * (|a0| * |b0| + c ^ 2) = 0 := by linear_combination h4
    rcases mul_eq_zero.mp h6 with h7 | h7
    · linarith
    · linarith [sq_nonneg c, mul_nonneg (abs_nonneg a0) (abs_nonneg b0)]
  have hgcdabs : Int.gcd |a0| |b0| = 1 := by
    rw [Int.gcd, Int.natAbs_abs, Int.natAbs_abs]
    exact Int.isCoprime_iff_gcd_eq_one.mp hcop
  obtain ⟨u, hu⟩ := sq_of_gcd_of_nonneg hgcdabs habs (abs_nonneg a0)
  obtain ⟨v, hv⟩ := sq_of_gcd_of_nonneg (by rwa [Int.gcd_comm]) (by rw [mul_comm]; exact habs)
    (abs_nonneg b0)
  refine ⟨u, v, ?_, ?_, ?_⟩
  · rw [ha0, ← sq_abs a0, hu]; ring
  · rw [hb0, ← sq_abs b0, hv]; ring
  · rw [← habs, hu, hv]

/-! ## Stage 2: concordant system to the quartic -/

lemma conc_to_quartic {g h z w : ℤ} (hgcd : Int.gcd g h = 1) (hg : g % 2 = 1)
    (h1 : g ^ 2 + h ^ 2 = z ^ 2) (h2 : g ^ 2 + 4 * h ^ 2 = w ^ 2) :
    ∃ m n : ℤ, Int.gcd m n = 1 ∧ (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) ∧
      h = m * n ∧ z ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 := by
  have hg0 : g ≠ 0 := by intro hh; rw [hh] at hg; norm_num at hg
  have hw0 : w ≠ 0 := by
    intro hh
    rw [hh] at h2
    have hg2 : g ^ 2 = 0 := by nlinarith [sq_nonneg h, sq_nonneg g]
    exact hg0 (by simpa using sq_eq_zero_iff.mp hg2)
  have hpt : PythagoreanTriple g (2 * h) |w| := by
    have habs : |w| * |w| = w * w := abs_mul_abs_self w
    show g * g + 2 * h * (2 * h) = |w| * |w|
    rw [habs]; linear_combination h2
  have hcop : Int.gcd g (2 * h) = 1 := by
    rw [← Int.isCoprime_iff_gcd_eq_one]
    exact IsCoprime.mul_right (Int.isCoprime_two_right.mpr (Int.odd_iff.mpr hg))
      (Int.isCoprime_iff_gcd_eq_one.mpr hgcd)
  obtain ⟨m, n, hgm, hhm, -, hmn, hpar, -⟩ :=
    hpt.coprime_classification' hcop hg (abs_pos.mpr hw0)
  have hh : h = m * n := by linarith
  refine ⟨m, n, hmn, hpar, hh, ?_⟩
  rw [hgm, hh] at h1
  linear_combination -h1


/-! ## Stage 3: size helpers -/

lemma one_le_sq {u : ℤ} (hu : u ≠ 0) : 1 ≤ u ^ 2 := by
  have h1 : 0 < u ^ 2 := lt_of_le_of_ne (sq_nonneg u) (Ne.symm (pow_ne_zero 2 hu))
  linarith [Int.add_one_le_iff.mpr h1]

lemma one_le_pow_four {u : ℤ} (hu : u ≠ 0) : 1 ≤ u ^ 4 := by
  nlinarith [one_le_sq hu]

lemma abs_le_pow_four (v : ℤ) : |v| ≤ v ^ 4 := by
  rcases eq_or_ne v 0 with rfl | hv0
  · norm_num
  · have h1 : 1 ≤ v ^ 2 := one_le_sq hv0
    have h2 : |v| ≤ v ^ 2 := by
      nlinarith [Int.one_le_abs hv0, abs_nonneg v, sq_abs v]
    nlinarith [h1]

/-! ## Stage 4: the two branches of the descent -/

/-- The branch `3 ∣ B` of the descent is impossible: `e² = 3t⁴ + 2s²t² − s⁴`
has no solution with `e` odd and `s`, `t` coprime, by congruences mod `8`. -/
lemma case_i_absurd {s t e : ℤ} (hst : Int.gcd s t = 1) (he : e % 2 = 1)
    (h : e ^ 2 = 3 * t ^ 4 + 2 * (s ^ 2 * t ^ 2) - s ^ 4) : False := by
  have he8 : e ^ 2 % 8 = 1 := odd_sq_emod_eight he
  have hcop : IsCoprime s t := Int.isCoprime_iff_gcd_eq_one.mpr hst
  rcases Int.emod_two_eq_zero_or_one s with hs2 | hs2 <;>
    rcases Int.emod_two_eq_zero_or_one t with ht2 | ht2
  · have h1 := hcop.isUnit_of_dvd' (⟨s / 2, by omega⟩ : (2 : ℤ) ∣ s)
      (⟨t / 2, by omega⟩ : (2 : ℤ) ∣ t)
    rw [Int.isUnit_iff] at h1
    omega
  · refine mod8_B (e ^ 2) (t ^ 4) (s ^ 4) (s ^ 2 * t ^ 2) he8 h
      (odd_pow_four_emod_eight ht2) (even_pow_four_emod_eight hs2) ?_
    obtain ⟨s1, hs1⟩ : ∃ x, s = 2 * x := ⟨s / 2, by omega⟩
    exact emod_four_zero (X := s1 ^ 2 * t ^ 2) (by rw [hs1]; ring)
  · refine mod8_C (e ^ 2) (t ^ 4) (s ^ 4) (s ^ 2 * t ^ 2) he8 h
      (even_pow_four_emod_eight ht2) (odd_pow_four_emod_eight hs2) ?_
    obtain ⟨t1, ht1⟩ : ∃ x, t = 2 * x := ⟨t / 2, by omega⟩
    exact emod_four_zero (X := s ^ 2 * t1 ^ 2) (by rw [ht1]; ring)
  · refine mod8_A (e ^ 2) (t ^ 4) (s ^ 4) (s ^ 2 * t ^ 2) he8 h
      (odd_pow_four_emod_eight ht2) (odd_pow_four_emod_eight hs2) ?_
    have h1 : s ^ 2 * t ^ 2 = (s * t) ^ 2 := by ring
    rw [h1]
    exact odd_sq_emod_eight (by rw [Int.mul_emod, hs2, ht2]; norm_num)

/-- The descent step proper. From `e² = v⁴ + 2u²v² − 3u⁴` with `u`, `v` coprime
and `e` odd, `u` is even and `v` is odd, and `(m, n)` with `u = mn` solves the
quartic with value `v`. -/
lemma quartic_step {u v e : ℤ} (huv : Int.gcd u v = 1) (he : e % 2 = 1)
    (h : e ^ 2 = v ^ 4 + 2 * (u ^ 2 * v ^ 2) - 3 * u ^ 4) :
    ∃ m n : ℤ, Int.gcd m n = 1 ∧ (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) ∧
      u = m * n ∧ v ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 := by
  have he8 : e ^ 2 % 8 = 1 := odd_sq_emod_eight he
  have hcopuv : IsCoprime u v := Int.isCoprime_iff_gcd_eq_one.mpr huv
  obtain ⟨hu2, hv2⟩ : u % 2 = 0 ∧ v % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one u with hu2 | hu2 <;>
      rcases Int.emod_two_eq_zero_or_one v with hv2 | hv2
    · exfalso
      have h1 := hcopuv.isUnit_of_dvd' (⟨u / 2, by omega⟩ : (2 : ℤ) ∣ u)
        (⟨v / 2, by omega⟩ : (2 : ℤ) ∣ v)
      rw [Int.isUnit_iff] at h1
      omega
    · exact ⟨hu2, hv2⟩
    · exfalso
      refine mod8_E (e ^ 2) (u ^ 4) (v ^ 4) (u ^ 2 * v ^ 2) he8 h
        (odd_pow_four_emod_eight hu2) (even_pow_four_emod_eight hv2) ?_
      obtain ⟨v1, hv1⟩ : ∃ x, v = 2 * x := ⟨v / 2, by omega⟩
      exact emod_four_zero (X := u ^ 2 * v1 ^ 2) (by rw [hv1]; ring)
    · exfalso
      refine mod8_D (e ^ 2) (u ^ 4) (v ^ 4) (u ^ 2 * v ^ 2) he8 h
        (odd_pow_four_emod_eight hu2) (odd_pow_four_emod_eight hv2) ?_
      have h1 : u ^ 2 * v ^ 2 = (u * v) ^ 2 := by ring
      rw [h1]
      exact odd_sq_emod_eight (by rw [Int.mul_emod, hu2, hv2]; norm_num)
  obtain ⟨u1, hu1⟩ : ∃ x, u = 2 * x := ⟨u / 2, by omega⟩
  obtain ⟨v1, hv1⟩ : ∃ x, v = 2 * x + 1 := ⟨v / 2, by omega⟩
  obtain ⟨aa, bb, hbez⟩ := hcopuv.pow (m := 2) (n := 2)
  have hjj : v ^ 2 - u ^ 2 = 4 * (v1 ^ 2 + v1 - u1 ^ 2) + 1 := by rw [hu1, hv1]; ring
  have hfact : (v ^ 2 - u ^ 2) * (v ^ 2 + 3 * u ^ 2) = e ^ 2 := by linear_combination -h
  have hcopfac : IsCoprime (v ^ 2 - u ^ 2) (v ^ 2 + 3 * u ^ 2) :=
    ⟨1 - (v1 ^ 2 + v1 - u1 ^ 2) * (3 * bb - aa), -((v1 ^ 2 + v1 - u1 ^ 2) * (aa + bb)), by
      linear_combination hjj + (-4 * (v1 ^ 2 + v1 - u1 ^ 2)) * hbez⟩
  have hv0 : v ≠ 0 := by intro hh; rw [hh] at hv2; norm_num at hv2
  have hSpos : 0 < v ^ 2 + 3 * u ^ 2 := by
    have h1 : 0 < v ^ 2 := lt_of_le_of_ne (sq_nonneg v) (Ne.symm (pow_ne_zero 2 hv0))
    linarith [sq_nonneg u]
  have hnn : 0 ≤ v ^ 2 - u ^ 2 := by
    by_contra hcon
    rw [not_le] at hcon
    have h1 : (v ^ 2 - u ^ 2) * (v ^ 2 + 3 * u ^ 2) < 0 := mul_neg_of_neg_of_pos hcon hSpos
    rw [hfact] at h1
    exact absurd h1 (not_lt.mpr (sq_nonneg e))
  have hgcdfac : Int.gcd (v ^ 2 - u ^ 2) (v ^ 2 + 3 * u ^ 2) = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp hcopfac
  obtain ⟨al, hal⟩ := sq_of_gcd_of_nonneg hgcdfac hfact hnn
  obtain ⟨be, hbe⟩ := sq_of_gcd_of_nonneg (by rwa [Int.gcd_comm])
    (by rw [mul_comm]; exact hfact) hSpos.le
  have halodd : al % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one al with h1 | h1
    · exfalso
      obtain ⟨t, ht⟩ : ∃ x, al = 2 * x := ⟨al / 2, by omega⟩
      exact four_mul_ne (X := t ^ 2) (Y := v1 ^ 2 + v1 - u1 ^ 2)
        (by linear_combination -hal + hjj - (al + 2 * t) * ht)
    · exact h1
  have hgcdalu : Int.gcd al u = 1 := by
    rw [← Int.isCoprime_iff_gcd_eq_one]
    have h1 : IsCoprime (al ^ 2) u :=
      ⟨bb, (aa + bb) * u, by linear_combination hbez - bb * hal⟩
    exact h1.of_isCoprime_of_dvd_left (dvd_pow_self al two_ne_zero)
  obtain ⟨m, n, hmn, hpar, hun, hquart⟩ :=
    conc_to_quartic (z := v) (w := be) hgcdalu halodd (by linear_combination -hal)
      (by linear_combination hbe - hal)
  exact ⟨m, n, hmn, hpar, hun, hquart⟩

/-! ## Stage 5: the descent -/

lemma quartic_descent_aux : ∀ (N : ℕ) (d e c : ℤ), c.natAbs < N → Int.gcd d e = 1 →
    d % 2 = 0 → e % 2 = 1 → d ^ 4 - d ^ 2 * e ^ 2 + e ^ 4 = c ^ 2 → d = 0 := by
  intro N
  induction N with
  | zero => intro _ _ _ hc _ _ _ _; exact absurd hc (Nat.not_lt_zero _)
  | succ N ih =>
    intro d e c hcN hgcd hd he heq
    by_contra hd0
    have hcopde : IsCoprime d e := Int.isCoprime_iff_gcd_eq_one.mpr hgcd
    obtain ⟨c₀, rfl⟩ : ∃ x, d = 2 * x := ⟨d / 2, by omega⟩
    have hc₀0 : c₀ ≠ 0 := fun hh => hd0 (by rw [hh]; ring)
    have he0 : e ≠ 0 := by intro hh; rw [hh] at he; norm_num at he
    have hcne : c ≠ 0 := by
      intro hh
      rw [hh] at heq
      have h1 : ((2 * c₀) ^ 2 - e ^ 2) ^ 2 + (2 * c₀ * e) ^ 2 = 0 := by linear_combination heq
      have h2 : (2 * c₀ * e) ^ 2 = 0 := by
        linarith [sq_nonneg ((2 * c₀) ^ 2 - e ^ 2), sq_nonneg (2 * c₀ * e)]
      have h3 : 2 * c₀ * e = 0 := sq_eq_zero_iff.mp h2
      rcases mul_eq_zero.mp h3 with h4 | h4
      · rcases mul_eq_zero.mp h4 with h5 | h5
        · norm_num at h5
        · exact hc₀0 h5
      · exact he0 h4
    obtain ⟨f, hfabs, hfpos, hf2⟩ : ∃ f : ℤ, f = |c| ∧ 0 < f ∧ f ^ 2 = c ^ 2 :=
      ⟨|c|, rfl, abs_pos.mpr hcne, sq_abs c⟩
    have hfsq : f ^ 2 = 16 * c₀ ^ 4 - 4 * c₀ ^ 2 * e ^ 2 + e ^ 4 := by
      rw [hf2]; linear_combination -heq
    have he4 : e ^ 4 % 8 = 1 := odd_pow_four_emod_eight he
    have hfodd : f % 2 = 1 := by
      rcases Int.emod_two_eq_zero_or_one f with h | h
      · exfalso
        obtain ⟨t, ht⟩ : ∃ x, f = 2 * x := ⟨f / 2, by omega⟩
        exact not_emod_eight_one_of_four_dvd (X := t ^ 2 - 4 * c₀ ^ 4 + c₀ ^ 2 * e ^ 2)
          (by linear_combination -hfsq + (f + 2 * t) * ht) he4
      · exact h
    obtain ⟨P, hP⟩ : ∃ P : ℤ, P = e ^ 2 - 2 * c₀ ^ 2 := ⟨_, rfl⟩
    have hPodd : P % 2 = 1 := by
      obtain ⟨ek, hek⟩ : ∃ x, e = 2 * x + 1 := ⟨e / 2, by omega⟩
      exact emod_two_one (X := 2 * ek ^ 2 + 2 * ek - c₀ ^ 2) (by rw [hP, hek]; ring)
    obtain ⟨A, hA⟩ : ∃ A, f - P = 2 * A := ⟨(f - P) / 2, by omega⟩
    obtain ⟨B, hB⟩ : ∃ B, f + P = 2 * B := ⟨(f + P) / 2, by omega⟩
    have hABf : A + B = f := by omega
    have hABP : B - A = P := by omega
    have hABprod : A * B = 3 * c₀ ^ 4 := by
      have h4 : (4 : ℤ) * (A * B) = 4 * (3 * c₀ ^ 4) := by
        linear_combination hfsq - (f + P) * hA - 2 * A * hB - (e ^ 2 - 2 * c₀ ^ 2 + P) * hP
      exact mul_left_cancel₀ (by norm_num) h4
    have hce : IsCoprime c₀ e := hcopde.of_isCoprime_of_dvd_left ⟨2, by ring⟩
    obtain ⟨aa0, bb0, hab0⟩ := hce
    have hcf : IsCoprime c₀ f := by
      refine ⟨aa0 ^ 4 * c₀ ^ 3 + 4 * aa0 ^ 3 * c₀ ^ 2 * bb0 * e + 6 * aa0 ^ 2 * c₀ * bb0 ^ 2 * e ^ 2
        + 4 * aa0 * bb0 ^ 3 * e ^ 3 - 16 * bb0 ^ 4 * c₀ ^ 3 + 4 * bb0 ^ 4 * c₀ * e ^ 2,
        bb0 ^ 4 * f, ?_⟩
      linear_combination ((aa0 * c₀ + bb0 * e) ^ 3 + (aa0 * c₀ + bb0 * e) ^ 2
        + (aa0 * c₀ + bb0 * e) + 1) * hab0 + bb0 ^ 4 * hfsq
    have hp3 : Prime (3 : ℤ) := Int.prime_iff_natAbs_prime.mpr Nat.prime_three
    have hABcop : Int.gcd A B = 1 := by
      have hdvd3 : ((Int.gcd A B : ℕ) : ℤ) ∣ 3 := by
        obtain ⟨ss, tt, hst⟩ := hcf.pow_left (m := 4)
        have h3 : (3 : ℤ) = ss * (A * B) + 3 * tt * (A + B) := by
          rw [hABprod, hABf]; linear_combination -3 * hst
        rw [h3]
        exact dvd_add (((Int.gcd_dvd_left A B).mul_right B).mul_left ss)
          ((dvd_add (Int.gcd_dvd_left A B) (Int.gcd_dvd_right A B)).mul_left (3 * tt))
      rcases (Nat.prime_three).eq_one_or_self_of_dvd (Int.gcd A B) (by exact_mod_cast hdvd3) with
        h | h
      · exact h
      · exfalso
        have h3A : (3 : ℤ) ∣ A := by
          have h1 : ((Int.gcd A B : ℕ) : ℤ) ∣ A := Int.gcd_dvd_left A B
          rw [h] at h1; exact_mod_cast h1
        have h3B : (3 : ℤ) ∣ B := by
          have h1 : ((Int.gcd A B : ℕ) : ℤ) ∣ B := Int.gcd_dvd_right A B
          rw [h] at h1; exact_mod_cast h1
        obtain ⟨A1, hA1⟩ := h3A
        obtain ⟨B1, hB1⟩ := h3B
        have hcdvd : (3 : ℤ) ∣ c₀ := by
          refine hp3.dvd_of_dvd_pow (n := 4) ⟨A1 * B1, ?_⟩
          have h1 : (3 : ℤ) * (3 * (A1 * B1)) = 3 * c₀ ^ 4 := by
            linear_combination hABprod - (3 * A1) * hB1 - B * hA1
          exact (mul_left_cancel₀ (by norm_num : (3 : ℤ) ≠ 0) h1).symm
        have hfdvd : (3 : ℤ) ∣ f := ⟨A1 + B1, by linarith⟩
        have h9 := hcf.isUnit_of_dvd' hcdvd hfdvd
        rw [Int.isUnit_iff] at h9
        omega
    have hc₀4pos : 0 < c₀ ^ 4 := by
      have h1 : 0 < c₀ ^ 2 := lt_of_le_of_ne (sq_nonneg c₀) (Ne.symm (pow_ne_zero 2 hc₀0))
      have h2 : c₀ ^ 4 = (c₀ ^ 2) ^ 2 := by ring
      rw [h2]; exact pow_pos h1 2
    have hprodpos : 0 < A * B := by rw [hABprod]; linarith
    have hApos : 0 < A := by
      rcases mul_pos_iff.mp hprodpos with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact h1
      · omega
    have hBpos : 0 < B := by
      rcases mul_pos_iff.mp hprodpos with ⟨-, h1⟩ | ⟨h1, h2⟩
      · exact h1
      · omega
    rcases hp3.2.2 A B ⟨c₀ ^ 4, hABprod⟩ with h3A | h3B
    · obtain ⟨A', hA'⟩ := h3A
      have hA'pos : 0 < A' := by omega
      have hA'B : A' * B = c₀ ^ 4 := by
        have h1 : (3 : ℤ) * (A' * B) = 3 * c₀ ^ 4 := by linear_combination hABprod - B * hA'
        exact mul_left_cancel₀ (by norm_num) h1
      have hA'cop : Int.gcd A' B = 1 := by
        rw [← Int.isCoprime_iff_gcd_eq_one]
        exact (Int.isCoprime_iff_gcd_eq_one.mpr hABcop).of_isCoprime_of_dvd_left ⟨3, by linarith⟩
      obtain ⟨u, v, hu4, hv4, hc₀2⟩ := fourth_power_split hA'pos hBpos hA'cop hA'B
      have huv : Int.gcd u v = 1 := by
        rw [← Int.isCoprime_iff_gcd_eq_one]
        have h1 : IsCoprime (u ^ 4) (v ^ 4) := by
          rw [← hu4, ← hv4]; exact Int.isCoprime_iff_gcd_eq_one.mpr hA'cop
        exact (h1.of_isCoprime_of_dvd_left (dvd_pow_self u (by norm_num))).of_isCoprime_of_dvd_right
          (dvd_pow_self v (by norm_num))
      have he2 : e ^ 2 = v ^ 4 + 2 * (u ^ 2 * v ^ 2) - 3 * u ^ 4 := by
        linear_combination -hP - hABP + hv4 - hA' - 3 * hu4 + 2 * hc₀2
      have hf3 : f = 3 * u ^ 4 + v ^ 4 := by
        linear_combination -hABf + hA' + 3 * hu4 + hv4
      have hu0 : u ≠ 0 := fun hh => hc₀0 (sq_eq_zero_iff.mp (by rw [hc₀2, hh]; ring))
      obtain ⟨m, n, hmn, hpar, hun, hquart⟩ := quartic_step huv he he2
      have hvlt : v.natAbs < N := by
        have h1 : |v| < f := by
          rw [hf3]; linarith [one_le_pow_four hu0, abs_le_pow_four v]
        have h4 : (v.natAbs : ℤ) < (c.natAbs : ℤ) := by
          rw [Int.natCast_natAbs, Int.natCast_natAbs, ← hfabs]; exact h1
        omega
      have hmn0 : m * n = 0 := by
        rcases hpar with ⟨hm2, hn2⟩ | ⟨hm2, hn2⟩
        · have h1 := ih m n v hvlt hmn hm2 hn2 (by linear_combination -hquart)
          rw [h1]; ring
        · have h1 := ih n m v hvlt (by rwa [Int.gcd_comm]) hn2 hm2
            (by linear_combination -hquart)
          rw [h1]; ring
      exact hu0 (by rw [hun]; exact hmn0)
    · obtain ⟨B', hB'⟩ := h3B
      have hB'pos : 0 < B' := by omega
      have hAB' : A * B' = c₀ ^ 4 := by
        have h1 : (3 : ℤ) * (A * B') = 3 * c₀ ^ 4 := by linear_combination hABprod - A * hB'
        exact mul_left_cancel₀ (by norm_num) h1
      have hABcop' : Int.gcd A B' = 1 := by
        rw [← Int.isCoprime_iff_gcd_eq_one]
        exact (Int.isCoprime_iff_gcd_eq_one.mpr hABcop).of_isCoprime_of_dvd_right ⟨3, by linarith⟩
      obtain ⟨s, t, hs4, ht4, hc₀2⟩ := fourth_power_split hApos hB'pos hABcop' hAB'
      have hst : Int.gcd s t = 1 := by
        rw [← Int.isCoprime_iff_gcd_eq_one]
        have h1 : IsCoprime (s ^ 4) (t ^ 4) := by
          rw [← hs4, ← ht4]; exact Int.isCoprime_iff_gcd_eq_one.mpr hABcop'
        exact (h1.of_isCoprime_of_dvd_left (dvd_pow_self s (by norm_num))).of_isCoprime_of_dvd_right
          (dvd_pow_self t (by norm_num))
      have he2 : e ^ 2 = 3 * t ^ 4 + 2 * (s ^ 2 * t ^ 2) - s ^ 4 := by
        linear_combination -hABP - hP + hB' + 3 * ht4 - hs4 + 2 * hc₀2
      exact case_i_absurd hst he he2

lemma quartic_no_sol {m n c : ℤ} (hmn : Int.gcd m n = 1)
    (hpar : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0)
    (h : m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 = c ^ 2) : m * n = 0 := by
  rcases hpar with ⟨hm, hn⟩ | ⟨hm, hn⟩
  · rw [quartic_descent_aux (c.natAbs + 1) m n c (by omega) hmn hm hn h]; ring
  · rw [quartic_descent_aux (c.natAbs + 1) n m c (by omega) (by rwa [Int.gcd_comm]) hn hm
      (by linear_combination h)]
    ring


/-! ## Stage 6: the integral quartic -/

lemma four_mul_ne3 {X Y : ℤ} (h : 4 * X = 4 * Y + 3) : False := by omega

lemma four_mul_ne13 {X Y : ℤ} (h : 4 * X + 1 = 4 * Y + 3) : False := by omega

lemma sq_ne_three_mod_four {al X : ℤ} (h : al ^ 2 = 4 * X + 3) : False := by
  rcases Int.emod_two_eq_zero_or_one al with h1 | h1
  · obtain ⟨t, ht⟩ : ∃ x, al = 2 * x := ⟨al / 2, by omega⟩
    exact four_mul_ne3 (X := t ^ 2) (Y := X) (by linear_combination h - (al + 2 * t) * ht)
  · obtain ⟨t, ht⟩ : ∃ x, al = 2 * x + 1 := ⟨al / 2, by omega⟩
    exact four_mul_ne13 (X := t ^ 2 + t) (Y := X)
      (by linear_combination h - (al + 2 * t + 1) * ht)

lemma odd_of_sq_eq_four_mul_add_one {al X : ℤ} (h : al ^ 2 = 4 * X + 1) : al % 2 = 1 := by
  rcases Int.emod_two_eq_zero_or_one al with h1 | h1
  · exfalso
    obtain ⟨t, ht⟩ : ∃ x, al = 2 * x := ⟨al / 2, by omega⟩
    exact four_mul_ne (X := t ^ 2) (Y := X) (by linear_combination h - (al + 2 * t) * ht)
  · exact h1

/-- The integral form: `r² = (p² − q²)(p² + 3q²)` with `p`, `q` coprime and
`q > 0` forces `r = 0`. -/
lemma quartic_int (p q r : ℤ) (hqpos : 0 < q) (hpq : Int.gcd p q = 1)
    (h : r ^ 2 = (p ^ 2 - q ^ 2) * (p ^ 2 + 3 * q ^ 2)) : r = 0 := by
  have hcop : IsCoprime p q := Int.isCoprime_iff_gcd_eq_one.mpr hpq
  obtain ⟨aa, bb, hbez⟩ := hcop.pow (m := 2) (n := 2)
  have hq0 : q ≠ 0 := hqpos.ne'
  have hSpos : 0 < p ^ 2 + 3 * q ^ 2 := by
    have h1 : 0 < q ^ 2 := lt_of_le_of_ne (sq_nonneg q) (Ne.symm (pow_ne_zero 2 hq0))
    linarith [sq_nonneg p]
  have hnn : 0 ≤ p ^ 2 - q ^ 2 := by
    by_contra hcon
    rw [not_le] at hcon
    have h1 : (p ^ 2 - q ^ 2) * (p ^ 2 + 3 * q ^ 2) < 0 := mul_neg_of_neg_of_pos hcon hSpos
    rw [← h] at h1
    exact absurd h1 (not_lt.mpr (sq_nonneg r))
  rcases Int.emod_two_eq_zero_or_one p with hp2 | hp2 <;>
    rcases Int.emod_two_eq_zero_or_one q with hq2 | hq2
  · exfalso
    have h1 := hcop.isUnit_of_dvd' (⟨p / 2, by omega⟩ : (2 : ℤ) ∣ p)
      (⟨q / 2, by omega⟩ : (2 : ℤ) ∣ q)
    rw [Int.isUnit_iff] at h1
    omega
  · -- `p` even, `q` odd: `p² − q² ≡ 3 mod 4`, and it must be a square
    exfalso
    obtain ⟨a, ha⟩ : ∃ x, p = 2 * x := ⟨p / 2, by omega⟩
    obtain ⟨b, hb⟩ : ∃ x, q = 2 * x + 1 := ⟨q / 2, by omega⟩
    have hD : p ^ 2 - q ^ 2 = 4 * (a ^ 2 - b ^ 2 - b - 1) + 3 := by rw [ha, hb]; ring
    have hcopDS : IsCoprime (p ^ 2 - q ^ 2) (p ^ 2 + 3 * q ^ 2) :=
      ⟨-1 + (a ^ 2 - b ^ 2 - b - 1 + 1) * (3 * aa - bb),
        (a ^ 2 - b ^ 2 - b - 1 + 1) * (aa + bb), by
        linear_combination -hD + (4 * (a ^ 2 - b ^ 2 - b - 1 + 1)) * hbez⟩
    obtain ⟨al, hal⟩ :=
      sq_of_gcd_of_nonneg (Int.isCoprime_iff_gcd_eq_one.mp hcopDS) h.symm hnn
    exact sq_ne_three_mod_four (al := al) (X := a ^ 2 - b ^ 2 - b - 1)
      (by linear_combination -hal + hD)
  · -- `p` odd, `q` even: reduces to the quartic, which forces `q = 0`
    exfalso
    obtain ⟨a, ha⟩ : ∃ x, p = 2 * x + 1 := ⟨p / 2, by omega⟩
    obtain ⟨b, hb⟩ : ∃ x, q = 2 * x := ⟨q / 2, by omega⟩
    have hD : p ^ 2 - q ^ 2 = 4 * (a ^ 2 + a - b ^ 2) + 1 := by rw [ha, hb]; ring
    have hcopDS : IsCoprime (p ^ 2 - q ^ 2) (p ^ 2 + 3 * q ^ 2) :=
      ⟨1 - (a ^ 2 + a - b ^ 2) * (3 * aa - bb), -((a ^ 2 + a - b ^ 2) * (aa + bb)), by
        linear_combination hD + (-4 * (a ^ 2 + a - b ^ 2)) * hbez⟩
    have hgcdDS : Int.gcd (p ^ 2 - q ^ 2) (p ^ 2 + 3 * q ^ 2) = 1 :=
      Int.isCoprime_iff_gcd_eq_one.mp hcopDS
    obtain ⟨al, hal⟩ := sq_of_gcd_of_nonneg hgcdDS h.symm hnn
    obtain ⟨be, hbe⟩ := sq_of_gcd_of_nonneg (by rwa [Int.gcd_comm])
      (by rw [mul_comm]; exact h.symm) hSpos.le
    have halodd : al % 2 = 1 :=
      odd_of_sq_eq_four_mul_add_one (al := al) (X := a ^ 2 + a - b ^ 2)
        (by linear_combination -hal + hD)
    have hgcdalq : Int.gcd al q = 1 := by
      rw [← Int.isCoprime_iff_gcd_eq_one]
      have h1 : IsCoprime (al ^ 2) q :=
        ⟨aa, (aa + bb) * q, by linear_combination hbez - aa * hal⟩
      exact h1.of_isCoprime_of_dvd_left (dvd_pow_self al two_ne_zero)
    obtain ⟨m, n, hmn, hpar, hun, hquart⟩ :=
      conc_to_quartic (z := p) (w := be) hgcdalq halodd (by linear_combination -hal)
        (by linear_combination hbe - hal)
    have h0 := quartic_no_sol hmn hpar hquart.symm
    omega
  · -- `p`, `q` both odd
    obtain ⟨a, ha⟩ : ∃ x, p = 2 * x + 1 := ⟨p / 2, by omega⟩
    obtain ⟨b, hb⟩ : ∃ x, q = 2 * x + 1 := ⟨q / 2, by omega⟩
    obtain ⟨A1, hA1⟩ : ∃ X : ℤ, p ^ 2 - q ^ 2 = 4 * X :=
      ⟨a ^ 2 + a - b ^ 2 - b, by rw [ha, hb]; ring⟩
    have hB1 : p ^ 2 + 3 * q ^ 2 = 4 * (A1 + q ^ 2) := by linear_combination hA1
    have hr2 : r ^ 2 = 16 * (A1 * (A1 + q ^ 2)) := by
      linear_combination h + (p ^ 2 + 3 * q ^ 2) * hA1 + 4 * A1 * hB1
    have hreven : r % 2 = 0 := by
      rcases Int.emod_two_eq_zero_or_one r with h1 | h1
      · exact h1
      · exfalso
        obtain ⟨t, ht⟩ : ∃ x, r = 2 * x + 1 := ⟨r / 2, by omega⟩
        exact four_mul_ne (X := 4 * (A1 * (A1 + q ^ 2))) (Y := t ^ 2 + t)
          (by linear_combination -hr2 + (r + 2 * t + 1) * ht)
    obtain ⟨r1, hr1⟩ : ∃ x, r = 2 * x := ⟨r / 2, by omega⟩
    have hr1sq : r1 ^ 2 = 4 * (A1 * (A1 + q ^ 2)) := by
      have h1 : (4 : ℤ) * r1 ^ 2 = 4 * (4 * (A1 * (A1 + q ^ 2))) := by
        linear_combination hr2 - (r + 2 * r1) * hr1
      exact mul_left_cancel₀ (by norm_num) h1
    have hr1even : r1 % 2 = 0 := by
      rcases Int.emod_two_eq_zero_or_one r1 with h1 | h1
      · exact h1
      · exfalso
        obtain ⟨t, ht⟩ : ∃ x, r1 = 2 * x + 1 := ⟨r1 / 2, by omega⟩
        exact four_mul_ne (X := A1 * (A1 + q ^ 2)) (Y := t ^ 2 + t)
          (by linear_combination -hr1sq + (r1 + 2 * t + 1) * ht)
    obtain ⟨rr, hrr⟩ : ∃ x, r1 = 2 * x := ⟨r1 / 2, by omega⟩
    have hrrsq : rr ^ 2 = A1 * (A1 + q ^ 2) := by
      have h1 : (4 : ℤ) * rr ^ 2 = 4 * (A1 * (A1 + q ^ 2)) := by
        linear_combination hr1sq - (r1 + 2 * rr) * hrr
      exact mul_left_cancel₀ (by norm_num) h1
    have hB1pos : 0 < A1 + q ^ 2 := by linarith
    have hA1nn : 0 ≤ A1 := by
      by_contra hcon
      rw [not_le] at hcon
      have h1 : A1 * (A1 + q ^ 2) < 0 := mul_neg_of_neg_of_pos hcon hB1pos
      rw [← hrrsq] at h1
      exact absurd h1 (not_lt.mpr (sq_nonneg rr))
    have hcopA1 : IsCoprime A1 (A1 + q ^ 2) :=
      ⟨3 * aa - bb, aa + bb, by linear_combination hbez - aa * hA1⟩
    obtain ⟨a1, ha1⟩ :=
      sq_of_gcd_of_nonneg (Int.isCoprime_iff_gcd_eq_one.mp hcopA1) hrrsq.symm hA1nn
    obtain ⟨b1, hb1⟩ := sq_of_gcd_of_nonneg
      (by rw [Int.gcd_comm]; exact Int.isCoprime_iff_gcd_eq_one.mp hcopA1)
      (by rw [mul_comm]; exact hrrsq.symm) hB1pos.le
    have hgcdqa1 : Int.gcd q a1 = 1 := by
      rw [← Int.isCoprime_iff_gcd_eq_one]
      have h1 : IsCoprime (a1 ^ 2) q :=
        ⟨4 * aa, (aa + bb) * q, by linear_combination hbez - aa * hA1 - 4 * aa * ha1⟩
      exact (h1.of_isCoprime_of_dvd_left (dvd_pow_self a1 two_ne_zero)).symm
    obtain ⟨m, n, hmn, hpar, hun, hquart⟩ :=
      conc_to_quartic (z := b1) (w := p) hgcdqa1 hq2 (by linear_combination hb1 - ha1)
        (by linear_combination -hA1 - 4 * ha1)
    have h0 := quartic_no_sol hmn hpar hquart.symm
    have ha10 : a1 = 0 := by rw [hun]; exact h0
    have hA10 : A1 = 0 := by rw [ha1, ha10]; ring
    have hrr0 : rr = 0 := by
      have h1 : rr ^ 2 = 0 := by rw [hrrsq, hA10]; ring
      exact sq_eq_zero_iff.mp h1
    omega

end MazurTwoTwelve.Quartic

/-- **The rational points of `X_1(2,12)`, in plane-quartic form**
(PROVEN 2026-07-25 by elementary descent; cut 2026-07-25 out of
`not_two_four_torsion_and_three_point`): the genus-`1` quartic
`v² = (j² − 1)(j² + 3) = j⁴ + 2j² − 3` has no rational point with
`v ≠ 0`.

This is the ONLY arithmetic input left in the `ℤ/2 × ℤ/12` exclusion;
everything between it and the group-theoretic statement is proven in
this file. It is a genuine rank-`0` Mordell–Weil fact, not formal:
`ellfromeqn` sends the quartic to `[0, 2, 0, 12, 24]`, the conductor-`24`
curve `24a`, of rank `0` with torsion `ℤ/4`. Its four rational points are
the two at infinity (the leading coefficient `1` is a square) and
`(±1, 0)`, so every AFFINE rational point has `v = 0` — which is the
statement.

The proof is the descent developed in `MazurTwoTwelve.Quartic` above.
Clearing denominators with `j = p/q` in lowest terms and
`r = v·q²` (an integer because `r² ∈ ℤ` and `Rat.mul_self_den`) gives
`r² = (p² − q²)(p² + 3q²)` with `gcd(p, q) = 1`, and
`MazurTwoTwelve.Quartic.quartic_int` forces `r = 0`.

Note the descent does NOT follow the classical route through
`d⁴ − d²e² + e⁴ = f²` split by the parity of `d`, `e`: that split leaves
the opposite-parity branch without a descent step (the obvious one
returns `{u, v} = {d, e}`), which is why the literature parametrises
`u² − uv + v² = w²` by Eisenstein triples in `ℤ[ω]` — machinery mathlib
does not have. The branch is closed here instead by factoring
`f² − (e² − 2c₀²)² = 12c₀⁴` and observing that one of the two coprime
cofactors of `3c₀⁴` gives `e² = 3t⁴ + 2s²t² − s⁴`, which is impossible
mod `8`. -/
theorem MazurTwoTwelve.quartic_only_trivial (j v : ℚ)
    (h : v ^ 2 = (j ^ 2 - 1) * (j ^ 2 + 3)) :
    v = 0 := by
  have hdpos : (0 : ℚ) < (j.den : ℚ) := by exact_mod_cast j.den_pos
  have hdne : ((j.den : ℚ)) ≠ 0 := ne_of_gt hdpos
  have hjq : (j.num : ℚ) = j * (j.den : ℚ) := by
    have h1 : (j.num : ℚ) / (j.den : ℚ) = j := Rat.num_div_den j
    rwa [div_eq_iff hdne] at h1
  obtain ⟨V, hVdef⟩ : ∃ V : ℚ, V = v * (j.den : ℚ) ^ 2 := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℤ,
      N = (j.num ^ 2 - (j.den : ℤ) ^ 2) * (j.num ^ 2 + 3 * (j.den : ℤ) ^ 2) := ⟨_, rfl⟩
  have hVsq : V * V = (N : ℚ) := by
    rw [hN, hVdef]
    push_cast
    rw [hjq]
    linear_combination ((j.den : ℚ)) ^ 4 * h
  have hVden : V.den = 1 := by
    have h1 : (V * V).den = V.den * V.den := Rat.mul_self_den V
    rw [hVsq, Rat.den_intCast] at h1
    exact Nat.dvd_one.mp ⟨V.den, h1⟩
  obtain ⟨r, hr⟩ : ∃ r : ℤ, (r : ℚ) = V := by
    refine ⟨V.num, ?_⟩
    have h1 : (V.num : ℚ) / (V.den : ℚ) = V := Rat.num_div_den V
    rw [hVden] at h1
    simpa using h1
  have hrr : r * r = N := by
    have h1 : ((r * r : ℤ) : ℚ) = ((N : ℤ) : ℚ) := by push_cast; rw [hr]; exact hVsq
    exact_mod_cast h1
  have hrz : r = 0 := by
    refine MazurTwoTwelve.Quartic.quartic_int j.num (j.den : ℤ) r (by exact_mod_cast j.den_pos) (by rw [Int.gcd, Int.natAbs_natCast]; exact j.reduced)
      ?_
    rw [← hN]
    linear_combination hrr
  have hV0 : V = 0 := by rw [← hr, hrz]; norm_num
  rw [hVdef] at hV0
  exact (mul_eq_zero.mp hV0).resolve_right (pow_ne_zero 2 hdne)

/-- **The normalised `X_1(2,12)` system has no rational solution**
(PROVEN 2026-07-25 from `quartic_only_trivial`): there is no rational
`(M, Z, W)` with `M ≠ 0`, `W ≠ 0`,
`3Z⁴ + 4(M² + 1)Z³ + 6M²Z² − M⁴ = 0` and
`W² = 4Z(Z + M²)(Z + 1)`.

`Z` is the abscissa of the order-`3` point, translated so that the
halved `2`-torsion abscissa is `0` and scaled so that the second square
difference is `1`; `M²` is the first square difference; `W` is
`2y + a₁x + a₃` at the order-`3` point. Reading the quartic as a
quadratic in `M²`, its discriminant is `16Z³(Z + 1)³`, so
`S = (2M² − 4Z³ − 6Z²)/(4Z(Z+1))` satisfies `S² = Z² + Z` — a conic with
the rational point at infinity, parametrised by `k = 2Z + 1 − 2S`
(`4kZ = (k − 1)²`, `4kS = 1 − k²`; note the SIGN of `S` is pinned by
this choice, which is why no case split on the two roots of the quadratic
survives — the other root is the parameter `1/k`). Then
`M² = 2Z³ + 3Z² + 2S³` gives `16k³M² = −(k − 1)³(3k + 1)` and hence
`16k³(Z + M²) = (k² − 1)²`; since `Z(Z+1) = S²`, the curve equation says
`Z + M²` is a square, so `k` is a square `j²`, and eliminating leaves
`(4jM/(j² − 1))² = (J² − 1)(J² + 3)` with `J = 1/j`. -/
theorem MazurTwoTwelve.no_rational_solution_normalized (M Z W : ℚ) (hM : M ≠ 0)
    (hpsi : 3 * Z ^ 4 + 4 * (M ^ 2 + 1) * Z ^ 3 + 6 * M ^ 2 * Z ^ 2 - M ^ 4 = 0)
    (hw : W ^ 2 = 4 * Z * (Z + M ^ 2) * (Z + 1)) (hW : W ≠ 0) : False := by
  -- nondegeneracy of the three factors
  have hprod : 4 * Z * (Z + M ^ 2) * (Z + 1) ≠ 0 := by
    rw [← hw]; exact pow_ne_zero 2 hW
  have hZ0 : Z ≠ 0 := fun h => hprod (by rw [h]; ring)
  have hZM : Z + M ^ 2 ≠ 0 := fun h => hprod (by rw [h]; ring)
  have hZ1 : Z + 1 ≠ 0 := fun h => hprod (by rw [h]; ring)
  have hden : (4 : ℚ) * Z * (Z + 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hZ0) hZ1
  -- the square root of the discriminant of the quadratic in `M²`
  obtain ⟨S, hS, hSD⟩ : ∃ S : ℚ, S ^ 2 = Z ^ 2 + Z ∧
      2 * M ^ 2 - 4 * Z ^ 3 - 6 * Z ^ 2 = S * (4 * Z * (Z + 1)) := by
    refine ⟨(2 * M ^ 2 - 4 * Z ^ 3 - 6 * Z ^ 2) / (4 * Z * (Z + 1)), ?_,
      (div_mul_cancel₀ _ hden).symm⟩
    rw [div_pow, div_eq_iff (pow_ne_zero 2 hden)]
    linear_combination (-4 : ℚ) * hpsi
  have hS0 : S ≠ 0 := by
    intro h
    rw [h] at hS
    exact hZ0 (by
      rcases mul_eq_zero.mp (show Z * (Z + 1) = 0 by linear_combination -hS) with h' | h'
      · exact h'
      · exact absurd h' hZ1)
  have hM2 : M ^ 2 = 2 * Z ^ 3 + 3 * Z ^ 2 + 2 * S ^ 3 := by
    linear_combination (1 / 2 : ℚ) * hSD - 2 * S * hS
  -- the rational parametrisation `Z = (k−1)²/4k`, `S = (1−k²)/4k` of `S² = Z² + Z`
  obtain ⟨k, hk0, hZk, hSk⟩ : ∃ k : ℚ, k ≠ 0 ∧ 4 * k * Z = (k - 1) ^ 2 ∧
      4 * k * S = 1 - k ^ 2 := by
    refine ⟨2 * Z + 1 - 2 * S, ?_, by linear_combination (-4 : ℚ) * hS,
      by linear_combination (-4 : ℚ) * hS⟩
    intro h
    have hcon : (0 : ℚ) = 1 := by
      linear_combination (-4 : ℚ) * hS - (2 * Z + 1 + 2 * S) * h
    norm_num at hcon
  have hk1 : k - 1 ≠ 0 := by
    intro h
    exact hZ0 (by
      have hk : k = 1 := by linarith
      rw [hk] at hZk; linarith)
  have hkm1 : k + 1 ≠ 0 := by
    intro h
    exact hZ1 (by
      have hk : k = -1 := by linarith
      rw [hk] at hZk; linarith)
  have hZval : Z = (k - 1) ^ 2 / (4 * k) := by
    field_simp; linarith [hZk]
  have hSval : S = (1 - k ^ 2) / (4 * k) := by
    field_simp; linarith [hSk]
  -- the two quantities in `k`
  have hMk : 16 * k ^ 3 * M ^ 2 = -((k - 1) ^ 3 * (3 * k + 1)) := by
    rw [hM2, hZval, hSval]; field_simp; ring
  have hZMk : 16 * k ^ 3 * (Z + M ^ 2) = (k ^ 2 - 1) ^ 2 := by
    linear_combination (4 * k ^ 2) * hZk + hMk
  -- `Z + M²` is a square, hence so is `k`
  have hsq : (Z + M ^ 2) * (2 * S) ^ 2 = W ^ 2 := by
    linear_combination (4 * (Z + M ^ 2)) * hS - hw
  obtain ⟨τ, hτ⟩ : ∃ τ : ℚ, τ ^ 2 = Z + M ^ 2 := by
    refine ⟨W / (2 * S), ?_⟩
    rw [div_pow, div_eq_iff (pow_ne_zero 2 (by simpa using hS0))]
    linear_combination -hsq
  have hτ0 : τ ≠ 0 := fun h => hZM (by rw [← hτ, h]; ring)
  have hk21 : k ^ 2 - 1 ≠ 0 := by
    intro h
    rcases mul_eq_zero.mp (show (k - 1) * (k + 1) = 0 by linear_combination h) with h' | h'
    · exact hk1 h'
    · exact hkm1 h'
  have hden2 : 4 * k * τ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hk0) hτ0
  obtain ⟨j, hj0, hjk⟩ : ∃ j : ℚ, j ≠ 0 ∧ k = j ^ 2 := by
    refine ⟨(k ^ 2 - 1) / (4 * k * τ), div_ne_zero hk21 hden2, ?_⟩
    rw [div_pow, eq_div_iff (pow_ne_zero 2 hden2)]
    linear_combination (16 * k ^ 3) * hτ + hZMk
  -- descend to the quartic
  subst hjk
  have hj1 : j ^ 2 - 1 ≠ 0 := hk1
  have hcore : (4 * j * M) ^ 2 * j ^ 4 =
      (1 - j ^ 2) * (1 + 3 * j ^ 2) * (j ^ 2 - 1) ^ 2 := by
    linear_combination hMk
  obtain ⟨J, hJ⟩ : ∃ J : ℚ, J * j = 1 := ⟨1 / j, by field_simp⟩
  have h1 : (J ^ 2 - 1) * (J ^ 2 + 3) * j ^ 4 = (1 - j ^ 2) * (1 + 3 * j ^ 2) := by
    linear_combination (J * j + 1) * ((J * j) ^ 2 + 1 + 2 * j ^ 2) * hJ
  have hV : (4 * j * M / (j ^ 2 - 1)) ^ 2 = (J ^ 2 - 1) * (J ^ 2 + 3) := by
    rw [div_pow, div_eq_iff (pow_ne_zero 2 hj1)]
    refine mul_right_cancel₀ (pow_ne_zero 4 hj0) ?_
    linear_combination hcore - (j ^ 2 - 1) ^ 2 * h1
  have hzero := MazurTwoTwelve.quartic_only_trivial J _ hV
  refine hM ?_
  have h4 : 4 * j * M = 0 := (div_eq_zero_iff.mp hzero).resolve_right hj1
  rcases mul_eq_zero.mp h4 with h' | h'
  · exact absurd ((mul_eq_zero.mp h').resolve_left (by norm_num)) hj0
  · exact h'

/-- **The `X_1(2,12)` system has no rational solution** (PROVEN
2026-07-25 by scaling to `no_rational_solution_normalized`): there is no
rational `(m, n, X, w)` with `m ≠ 0`, `n ≠ 0`, `w ≠ 0`,
`3X⁴ + 4(m² + n²)X³ + 6m²n²X² − m⁴n⁴ = 0` and
`w² = 4X(X + m²)(X + n²)`.

The hypothesis `m² ≠ n²` (the two unhalved `2`-torsion abscissae being
distinct) is passed by the consumer but NOT used: it is `_hmn`. That is
not a gap — the `m² = n²` locus is disposed of by the same argument
(the quartic then factors as `(Z + 1)³(3Z − 1)` after scaling, and
`Z = 1/3` makes `w² = 64/27`, not a rational square), so the leaf is
simply true without it. Keeping it in the signature records what the
geometry actually supplies. -/
theorem MazurTwoTwelve.no_rational_solution (m n X w : ℚ) (hm : m ≠ 0) (hn : n ≠ 0)
    (_hmn : m ^ 2 ≠ n ^ 2)
    (hpsi : 3 * X ^ 4 + 4 * (m ^ 2 + n ^ 2) * X ^ 3 + 6 * m ^ 2 * n ^ 2 * X ^ 2
      - m ^ 4 * n ^ 4 = 0)
    (hw : w ^ 2 = 4 * X * (X + m ^ 2) * (X + n ^ 2)) (hw0 : w ≠ 0) :
    False := by
  refine MazurTwoTwelve.no_rational_solution_normalized (m / n) (X / n ^ 2) (w / n ^ 3)
    (div_ne_zero hm hn) ?_ ?_ (div_ne_zero hw0 (pow_ne_zero 3 hn))
  · field_simp
    linear_combination hpsi
  · field_simp
    linear_combination hw

/-- **No rational `ℤ/2 × ℤ/4` together with a rational point of order
`3`** (PROVEN 2026-07-25 modulo the single quartic leaf
`MazurTwoTwelve.quartic_only_trivial`): no elliptic curve over `ℚ` has
an injective `ℤ/2 × ℤ/4 →+ E(ℚ)` and a rational point of order `3`
simultaneously. Such a curve carries a rational level structure
classified by the modular curve `X_1(2,12)`, a genus-one curve of
Mordell–Weil rank `0` over `ℚ` whose rational points are all cusps
(Kenku; subsumed in Mazur 1977, Thm 8).

The hypotheses say exactly that `E(ℚ)` contains `ℤ/2 × ℤ/12` (order
`24`), the second `ℤ/2 × ℤ/2m` beyond Mazur's list; `ℤ/12`,
`ℤ/2 × ℤ/6` and `ℤ/2 × ℤ/8` are all permitted, so no other node here
implies it.

The 2026-07-25 `IRREDUCIBLE` audit is SUPERSEDED. It rejected the
elementary route on the ground that "the `ℤ/2 × ℤ/4` gives ONE square
condition `(θ_T − θ_U)(θ_T − θ_V) = □` from `halving_square`, and the
sign contradiction of `not_full_four_torsion_rat` needs all three".
That undercounted: halving `T` makes `θ_T − θ_U` and `θ_T − θ_V`
SEPARATELY squares (`MazurTwoTwelve.halving_squares`), which is two
conditions, and the order-`3` point supplies a third equation through
the inflection identity — enough to cut `X_1(2,12)` down to a plane
quartic without any modular machinery. The audit's second point stands:
reduction plus Hasse only bounds the conductor.

Proof: full `2`-torsion `T = ψ(0,2)`, `U = ψ(1,0)`, `V = ψ(1,2)` with
`ψ(0,1)` halving `T`; `cubic_vieta` identifies the abscissae as the
roots of the `2`-division cubic; `halving_squares` writes
`θ_T − θ_U = m²`, `θ_T − θ_V = n²`; `exists_order_three_coords` gives
the inflection data of `Q`; and `(μw)² = μ²w²` produces the `3`-division
equation, which `MazurTwoTwelve.no_rational_solution` refutes. -/
theorem WeierstrassCurve.not_two_four_torsion_and_three_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (ψ : (ZMod 2 × ZMod 4) →+ (E⁄ℚ).Point) (hψ : Function.Injective ψ)
    (Q : (E⁄ℚ).Point) (hQ : addOrderOf Q = 3) :
    False := by
  -- the doubling relation for the order-`4` element `(0,1)`
  have hdb : ψ (0, 1) + ψ (0, 1) = ψ (0, 2) := by
    rw [← map_add]; exact congrArg ψ (by decide)
  -- the three nonzero `2`-torsion points
  have htorT : ψ (0, 2) + ψ (0, 2) = 0 := by
    rw [← map_add, show ((0 : ZMod 2), (2 : ZMod 4)) + (0, 2) = 0 by decide, map_zero]
  have htorU : ψ (1, 0) + ψ (1, 0) = 0 := by
    rw [← map_add, show ((1 : ZMod 2), (0 : ZMod 4)) + (1, 0) = 0 by decide, map_zero]
  have htorV : ψ (1, 2) + ψ (1, 2) = 0 := by
    rw [← map_add, show ((1 : ZMod 2), (2 : ZMod 4)) + (1, 2) = 0 by decide, map_zero]
  have hneT : ψ (0, 2) ≠ 0 := fun h =>
    absurd (hψ (h.trans (map_zero ψ).symm)) (by decide)
  have hneU : ψ (1, 0) ≠ 0 := fun h =>
    absurd (hψ (h.trans (map_zero ψ).symm)) (by decide)
  have hneV : ψ (1, 2) ≠ 0 := fun h =>
    absurd (hψ (h.trans (map_zero ψ).symm)) (by decide)
  have hneTU : ψ (0, 2) ≠ ψ (1, 0) := fun h => absurd (hψ h) (by decide)
  have hneTV : ψ (0, 2) ≠ ψ (1, 2) := fun h => absurd (hψ h) (by decide)
  have hneUV : ψ (1, 0) ≠ ψ (1, 2) := fun h => absurd (hψ h) (by decide)
  -- coordinates of the three `2`-torsion points and of the halving
  obtain ⟨θT, uT, xP, yP, lP, ⟨hnsT, hTeq⟩, hET, huT, hEP, hlP, hxP⟩ :=
    MazurFourTorsion.exists_halving_coords _ _ hdb htorT hneT
  obtain ⟨θU, uU, ⟨hnsU, hUeq⟩, hEU, huU⟩ :=
    MazurTwoTwelve.exists_two_torsion_coords _ htorU hneU
  obtain ⟨θV, uV, ⟨hnsV, hVeq⟩, hEV, huV⟩ :=
    MazurTwoTwelve.exists_two_torsion_coords _ htorV hneV
  rw [negY] at huT huU huV
  rw [equation_iff] at hET hEU hEV hEP
  -- distinct `2`-torsion points have distinct abscissae
  have hdTU : θT ≠ θU := by
    intro h; subst h
    have huu : uT = uU := by linarith
    subst huu
    rw [hTeq, hUeq] at hneTU; exact hneTU rfl
  have hdTV : θT ≠ θV := by
    intro h; subst h
    have huu : uT = uV := by linarith
    subst huu
    rw [hTeq, hVeq] at hneTV; exact hneTV rfl
  have hdUV : θU ≠ θV := by
    intro h; subst h
    have huu : uU = uV := by linarith
    subst huu
    rw [hUeq, hVeq] at hneUV; exact hneUV rfl
  -- the abscissae are the roots of the `2`-division cubic
  have hrootT : 4 * θT ^ 3 + ((E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂) * θT ^ 2 +
      (2 * (E⁄ℚ).a₁ * (E⁄ℚ).a₃ + 4 * (E⁄ℚ).a₄) * θT +
      ((E⁄ℚ).a₃ ^ 2 + 4 * (E⁄ℚ).a₆) = 0 := by
    linear_combination (2 * uT + (E⁄ℚ).a₁ * θT + (E⁄ℚ).a₃) * huT - 4 * hET
  have hrootU : 4 * θU ^ 3 + ((E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂) * θU ^ 2 +
      (2 * (E⁄ℚ).a₁ * (E⁄ℚ).a₃ + 4 * (E⁄ℚ).a₄) * θU +
      ((E⁄ℚ).a₃ ^ 2 + 4 * (E⁄ℚ).a₆) = 0 := by
    linear_combination (2 * uU + (E⁄ℚ).a₁ * θU + (E⁄ℚ).a₃) * huU - 4 * hEU
  have hrootV : 4 * θV ^ 3 + ((E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂) * θV ^ 2 +
      (2 * (E⁄ℚ).a₁ * (E⁄ℚ).a₃ + 4 * (E⁄ℚ).a₄) * θV +
      ((E⁄ℚ).a₃ ^ 2 + 4 * (E⁄ℚ).a₆) = 0 := by
    linear_combination (2 * uV + (E⁄ℚ).a₁ * θV + (E⁄ℚ).a₃) * huV - 4 * hEV
  obtain ⟨hB, hC, hD⟩ :=
    MazurFourTorsion.cubic_vieta hdTU hdTV hdUV hrootT hrootU hrootV
  -- BOTH differences at the halved abscissa are squares
  obtain ⟨m, n, hm, hn⟩ :=
    MazurTwoTwelve.halving_squares hEP hB hC hD hlP hxP hdTU hdTV hdUV
  -- nondegeneracy, recorded before normalising the abscissae away
  have hm0 : m ≠ 0 := by
    intro h
    refine hdTU ?_
    have h0 : θT - θU = 0 := by rw [hm, h]; ring
    linarith
  have hn0 : n ≠ 0 := by
    intro h
    refine hdTV ?_
    have h0 : θT - θV = 0 := by rw [hn, h]; ring
    linarith
  have hmn : m ^ 2 ≠ n ^ 2 := by
    intro h
    exact hdUV (by linarith)
  -- the order-`3` point is an inflection
  have hQ0 : Q ≠ 0 := by
    intro h; rw [h, addOrderOf_zero] at hQ; norm_num at hQ
  have h3Q : (3 : ℕ) • Q = 0 := by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q
  have hQ3 : Q + Q = -Q := by
    have h : Q + Q + Q = 0 := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, two_nsmul, one_nsmul] at h3Q
      exact h3Q
    exact eq_neg_of_add_eq_zero_left h
  obtain ⟨xQ, yQ, lQ, hEQ, hwQ0, hlQ, hxQ⟩ :=
    MazurTwoTwelve.exists_order_three_coords Q hQ0 hQ3
  rw [equation_iff] at hEQ
  -- normalise the two unhalved abscissae to `θT - m²`, `θT - n²`
  have hUsub : θU = θT - m ^ 2 := by linarith
  have hVsub : θV = θT - n ^ 2 := by linarith
  subst hUsub
  subst hVsub
  -- the three identities in `X = xQ - θT`
  have hwsq : (2 * yQ + (E⁄ℚ).a₁ * xQ + (E⁄ℚ).a₃) ^ 2 =
      4 * (xQ - θT) * ((xQ - θT) + m ^ 2) * ((xQ - θT) + n ^ 2) := by
    linear_combination 4 * hEQ + xQ ^ 2 * hB + xQ * hC + hD
  have hmu : (lQ + (E⁄ℚ).a₁ / 2) ^ 2 = 3 * (xQ - θT) + m ^ 2 + n ^ 2 := by
    linear_combination hxQ + (1 : ℚ) / 4 * hB
  have hmuw : (lQ + (E⁄ℚ).a₁ / 2) * (2 * yQ + (E⁄ℚ).a₁ * xQ + (E⁄ℚ).a₃) =
      3 * (xQ - θT) ^ 2 + 2 * (m ^ 2 + n ^ 2) * (xQ - θT) + m ^ 2 * n ^ 2 := by
    linear_combination hlQ + xQ / 2 * hB + (1 : ℚ) / 4 * hC
  -- eliminating the slope gives the `3`-division equation
  have hsq : (3 * (xQ - θT) ^ 2 + 2 * (m ^ 2 + n ^ 2) * (xQ - θT) + m ^ 2 * n ^ 2) ^ 2 =
      (3 * (xQ - θT) + m ^ 2 + n ^ 2) *
        (4 * (xQ - θT) * ((xQ - θT) + m ^ 2) * ((xQ - θT) + n ^ 2)) := by
    linear_combination
      (-((3 * (xQ - θT) ^ 2 + 2 * (m ^ 2 + n ^ 2) * (xQ - θT) + m ^ 2 * n ^ 2) +
          (lQ + (E⁄ℚ).a₁ / 2) * (2 * yQ + (E⁄ℚ).a₁ * xQ + (E⁄ℚ).a₃))) * hmuw +
        (2 * yQ + (E⁄ℚ).a₁ * xQ + (E⁄ℚ).a₃) ^ 2 * hmu +
        (3 * (xQ - θT) + m ^ 2 + n ^ 2) * hwsq
  have hpsi : 3 * (xQ - θT) ^ 4 + 4 * (m ^ 2 + n ^ 2) * (xQ - θT) ^ 3 +
      6 * m ^ 2 * n ^ 2 * (xQ - θT) ^ 2 - m ^ 4 * n ^ 4 = 0 := by
    linear_combination -hsq
  exact MazurTwoTwelve.no_rational_solution m n (xQ - θT)
    (2 * yQ + (E⁄ℚ).a₁ * xQ + (E⁄ℚ).a₃) hm0 hn0 hmn hpsi hwsq hwQ0

/-- **Exclusion of rational `ℤ/2 × ℤ/12`** (DERIVED 2026-07-23 from
the leaf `not_two_four_torsion_and_three_point` by splitting off the
`2`- and `3`-primary parts of `ℤ/2 × ℤ/12`): the modular curve
`X_1(2,12)` has no non-cuspidal rational point (Mazur 1977; the list
of fifteen). The subgroup `ℤ/2 × ⟨(0,3)⟩` is a `ℤ/2 × ℤ/4` level
structure and `φ(0,4)` has exact order `3`. -/
theorem WeierstrassCurve.not_two_twelve_torsion (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (φ : (ZMod 2 × ZMod 12) →+ (E⁄ℚ).Point) :
    ¬ Function.Injective φ := by
  intro hφ
  -- the `2`-primary embedding `ℤ/2 × ℤ/4 ↪ ℤ/2 × ℤ/12`
  obtain ⟨g, hg⟩ := ZMod.exists_injective_addMonoidHom_of_dvd
    (by norm_num : (0 : ℕ) < 4) (by norm_num : (4 : ℕ) ∣ 12) (by norm_num)
  have hgg : Function.Injective ((AddMonoidHom.id (ZMod 2)).prodMap g) := by
    rw [AddMonoidHom.coe_prodMap]
    exact Function.Injective.prodMap (fun _ _ h => h) hg
  -- the point of order `3`
  have hQ : addOrderOf (φ ((0 : ZMod 2), (4 : ZMod 12))) = 3 := by
    rw [addOrderOf_injective φ hφ]
    haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
    exact addOrderOf_eq_prime (by decide) (by decide)
  exact E.not_two_four_torsion_and_three_point
    (φ.comp ((AddMonoidHom.id (ZMod 2)).prodMap g)) (hφ.comp hgg) _ hQ

set_option backward.isDefEq.respectTransparency false in
/-- **No rational `(ℤ/2)³`** (PROVEN 2026-07-22): the geometric
`2`-torsion of an elliptic curve has exactly `2² = 4` points
(`TorsionCard.card_torsionBy`), so already over `ℚ̄` there is no
injective `(ℤ/2)³`; a rational one would base-change to one. -/
theorem WeierstrassCurve.not_two_cube_torsion (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (φ : (ZMod 2 × ZMod 2 × ZMod 2) →+ (E⁄ℚ).Point) :
    ¬ Function.Injective φ := by
  classical
  intro hφ
  -- the geometric `2`-torsion has `4` elements
  have hcard : Nat.card ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion 2) = 2 ^ 2 :=
    TorsionCard.card_torsionBy (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) 2
      (Nat.cast_ne_zero.mpr two_ne_zero)
  haveI hfin : Finite ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion 2) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  -- every element of `(ℤ/2)³` is killed by `2`
  have h2ann : ∀ z : ZMod 2 × ZMod 2 × ZMod 2, (2 : ℕ) • z = 0 := by decide
  -- base-change the embedding to `ℚ̄` and corestrict to the `2`-torsion
  let ψ : (ZMod 2 × ZMod 2 × ZMod 2) →+ (E⁄(AlgebraicClosure ℚ)).Point :=
    (Affine.Point.map (W' := E) (Algebra.ofId ℚ (AlgebraicClosure ℚ))).comp φ
  let f : (ZMod 2 × ZMod 2 × ZMod 2) → (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion 2 :=
    fun z => ⟨show ((E.map (algebraMap ℚ (AlgebraicClosure ℚ)))⁄(AlgebraicClosure ℚ)).Point from
      ψ z, by
        rw [Submodule.mem_torsionBy_iff]
        show ((2 : ℕ) : ℤ) • (ψ z) = 0
        rw [natCast_zsmul, ← map_nsmul, h2ann z, map_zero]⟩
  have hfinj : Function.Injective f := by
    intro z z' hzz
    have h1 : ψ z = ψ z' := congrArg Subtype.val hzz
    have h2 : Affine.Point.map (W' := E) (Algebra.ofId ℚ (AlgebraicClosure ℚ)) (φ z) =
        Affine.Point.map (W' := E) (Algebra.ofId ℚ (AlgebraicClosure ℚ)) (φ z') := h1
    exact hφ (Affine.Point.map_injective (W' := E)
      (f := Algebra.ofId ℚ (AlgebraicClosure ℚ)) h2)
  have hle : Nat.card (ZMod 2 × ZMod 2 × ZMod 2) ≤
      Nat.card ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion 2) :=
    Nat.card_le_card_of_injective f hfinj
  rw [hcard, Nat.card_prod, Nat.card_prod, Nat.card_zmod] at hle
  norm_num at hle

open scoped Function in
set_option backward.isDefEq.respectTransparency false in
/-- **Rank-`≤ 2` structure of the candidate torsion groups** (PROVEN
2026-07-22 — PURE FINITE ABELIAN GROUP THEORY, no arithmetic input): a
finite abelian group containing no subgroup `(ℤ/n)²` for any `n ≥ 3`
and no subgroup `(ℤ/2)³` is isomorphic to `ℤ/d × ℤ/n` with
`d ∈ {1, 2}`. Bookkeeping over the structure theorem
(`AddCommGroup.equiv_directSum_zmod_of_finite`): two prime-power
factors at the same odd prime `q` would give `(ℤ/q)²`, two `2`-power
factors of exponents `≥ 2` would give `(ℤ/4)²`, and three even factors
would give `(ℤ/2)³` — so at most one factor per odd prime, and the
`2`-part is at worst `ℤ/2 × ℤ/2^k`. Splitting off the (single) `ℤ/2`
factor if present, the remaining factors are pairwise coprime and merge
into a single cyclic group by the Chinese remainder theorem
(`ZMod.prodEquivPi`). -/
theorem AddCommGroup.exists_rank_le_two_decomposition
    (T : Type*) [AddCommGroup T] [Finite T]
    (hfull : ∀ n : ℕ, 3 ≤ n → ∀ φ : (ZMod n × ZMod n) →+ T, ¬ Function.Injective φ)
    (hcube : ∀ φ : (ZMod 2 × ZMod 2 × ZMod 2) →+ T, ¬ Function.Injective φ) :
    ∃ (d n : ℕ), (d = 1 ∨ d = 2) ∧ Nonempty (T ≃+ (ZMod d × ZMod n)) := by
  classical
  obtain ⟨ι, hι, p, hp, e, ⟨eqv0⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite T
  haveI := hι
  set a : ι → ℕ := fun i => p i ^ e i
  have hapos : ∀ i, 0 < a i := fun i => pow_pos (hp i).pos _
  let eqv : T ≃+ ∀ i, ZMod (a i) := eqv0.trans (DirectSum.addEquivProd _)
  -- (i) two distinct factors both divisible by `m ≥ 3` embed `(ℤ/m)²`
  have hpair : ∀ (m : ℕ), 3 ≤ m → ∀ i j : ι, i ≠ j → m ∣ a i → m ∣ a j → False := by
    intro m hm i j hij hdi hdj
    obtain ⟨gi, hgi⟩ := ZMod.exists_injective_addMonoidHom_of_dvd
      (by omega) hdi (hapos i)
    obtain ⟨gj, hgj⟩ := ZMod.exists_injective_addMonoidHom_of_dvd
      (by omega) hdj (hapos j)
    let Φ : (ZMod m × ZMod m) →+ ∀ k, ZMod (a k) :=
      ((AddMonoidHom.single (fun k => ZMod (a k)) i).comp gi).coprod
        ((AddMonoidHom.single (fun k => ZMod (a k)) j).comp gj)
    have hΦ : Function.Injective Φ := by
      intro x y hxy
      have hxi : Φ x i = Φ y i := congrFun hxy i
      have hxj : Φ x j = Φ y j := congrFun hxy j
      simp only [Φ, AddMonoidHom.coprod_apply, AddMonoidHom.comp_apply,
        AddMonoidHom.single_apply, Pi.add_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij.symm,
        add_zero, zero_add] at hxi hxj
      exact Prod.ext (hgi hxi) (hgj hxj)
    exact hfull m hm ((eqv.symm.toAddMonoidHom).comp Φ)
      ((eqv.symm.injective).comp hΦ)
  -- (ii) three distinct even factors embed `(ℤ/2)³`
  have htriple : ∀ i j k : ι, i ≠ j → i ≠ k → j ≠ k →
      2 ∣ a i → 2 ∣ a j → 2 ∣ a k → False := by
    intro i j k hij hik hjk hdi hdj hdk
    obtain ⟨gi, hgi⟩ := ZMod.exists_injective_addMonoidHom_of_dvd
      (by omega) hdi (hapos i)
    obtain ⟨gj, hgj⟩ := ZMod.exists_injective_addMonoidHom_of_dvd
      (by omega) hdj (hapos j)
    obtain ⟨gk, hgk⟩ := ZMod.exists_injective_addMonoidHom_of_dvd
      (by omega) hdk (hapos k)
    let Φ : (ZMod 2 × ZMod 2 × ZMod 2) →+ ∀ l, ZMod (a l) :=
      ((AddMonoidHom.single (fun l => ZMod (a l)) i).comp gi).coprod
        ((((AddMonoidHom.single (fun l => ZMod (a l)) j).comp gj).coprod
          ((AddMonoidHom.single (fun l => ZMod (a l)) k).comp gk)))
    have hΦ : Function.Injective Φ := by
      intro x y hxy
      have hxi : Φ x i = Φ y i := congrFun hxy i
      have hxj : Φ x j = Φ y j := congrFun hxy j
      have hxk : Φ x k = Φ y k := congrFun hxy k
      simp only [Φ, AddMonoidHom.coprod_apply, AddMonoidHom.comp_apply,
        AddMonoidHom.single_apply, Pi.add_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij.symm,
        Pi.single_eq_of_ne hik, Pi.single_eq_of_ne hik.symm,
        Pi.single_eq_of_ne hjk, Pi.single_eq_of_ne hjk.symm,
        add_zero, zero_add] at hxi hxj hxk
      exact Prod.ext (hgi hxi) (Prod.ext (hgj hxj) (hgk hxk))
    exact hcube ((eqv.symm.toAddMonoidHom).comp Φ)
      ((eqv.symm.injective).comp hΦ)
  -- the genuinely-even factors
  set S₂ : Finset ι := Finset.univ.filter (fun i => p i = 2 ∧ 1 ≤ e i) with hS₂
  have hS₂mem : ∀ {i}, i ∈ S₂ ↔ p i = 2 ∧ 1 ≤ e i := fun {i} => by
    simp [hS₂]
  have hdvd2 : ∀ {i}, i ∈ S₂ → 2 ∣ a i := by
    intro i hi
    rcases hS₂mem.mp hi with ⟨hp2, he⟩
    show 2 ∣ p i ^ e i
    rw [hp2]
    exact dvd_pow_self 2 (by omega)
  -- distinct same-prime genuine factors force the prime to be `2`
  have hsameprime : ∀ i j : ι, i ≠ j → 1 ≤ e i → 1 ≤ e j → p i = p j →
      p i = 2 := by
    intro i j hij hei hej hpp
    by_contra hne2
    have h3 : 3 ≤ p i := by
      have h2 := (hp i).two_le
      omega
    refine hpair (p i) h3 i j hij (dvd_pow_self (p i) (by omega)) ?_
    rw [hpp]
    show p j ∣ p j ^ e j
    exact dvd_pow_self (p j) (by omega)
  -- at most two genuinely-even factors
  have hS₂card : S₂.card ≤ 2 := by
    by_contra hgt
    obtain ⟨u, husub, hucard⟩ := Finset.exists_subset_card_eq (show 3 ≤ S₂.card by omega)
    obtain ⟨i, j, k, hij, hik, hjk, rfl⟩ := Finset.card_eq_three.mp hucard
    exact htriple i j k hij hik hjk
      (hdvd2 (husub (by simp))) (hdvd2 (husub (by simp))) (hdvd2 (husub (by simp)))
  by_cases hcard2 : S₂.card = 2
  · -- the `2`-part is `ℤ/2 × ℤ/2^k`: split off the `ℤ/2` factor
    obtain ⟨i₀, j₀, hij₀, hS₂eq⟩ := Finset.card_eq_two.mp hcard2
    have hi₀ : p i₀ = 2 ∧ 1 ≤ e i₀ := hS₂mem.mp (by rw [hS₂eq]; simp)
    have hj₀ : p j₀ = 2 ∧ 1 ≤ e j₀ := hS₂mem.mp (by rw [hS₂eq]; simp)
    -- one of the two exponents is exactly `1` (else `(ℤ/4)²`)
    have hnot44 : ¬ (2 ≤ e i₀ ∧ 2 ≤ e j₀) := by
      rintro ⟨h2i, h2j⟩
      refine hpair 4 (by norm_num) i₀ j₀ hij₀ ?_ ?_
      · show 4 ∣ p i₀ ^ e i₀
        rw [hi₀.1]
        exact (show (4 : ℕ) = 2 ^ 2 from rfl) ▸ pow_dvd_pow 2 h2i
      · show 4 ∣ p j₀ ^ e j₀
        rw [hj₀.1]
        exact (show (4 : ℕ) = 2 ^ 2 from rfl) ▸ pow_dvd_pow 2 h2j
    obtain ⟨i₁, j₁, _, hS₂eq', hei₁⟩ :
        ∃ i₁ j₁ : ι, i₁ ≠ j₁ ∧ S₂ = {i₁, j₁} ∧ e i₁ = 1 := by
      rcases (show e i₀ = 1 ∨ e j₀ = 1 by
        rcases hi₀ with ⟨-, h1⟩; rcases hj₀ with ⟨-, h2⟩; omega) with h1 | h1
      · exact ⟨i₀, j₀, hij₀, hS₂eq, h1⟩
      · exact ⟨j₀, i₀, hij₀.symm, by rw [hS₂eq, Finset.pair_comm], h1⟩
    have hi₁ : p i₁ = 2 ∧ 1 ≤ e i₁ := hS₂mem.mp (by rw [hS₂eq']; simp)
    -- the factors away from `i₁` are pairwise coprime
    have hcop' : Pairwise (Nat.Coprime on fun x : {x : ι // x ≠ i₁} => a x.1) := by
      intro x y hxy
      show Nat.Coprime (p x.1 ^ e x.1) (p y.1 ^ e y.1)
      have hne : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
      rcases Nat.eq_zero_or_pos (e x.1) with hex | hex
      · rw [hex, pow_zero]; exact Nat.coprime_one_left _
      rcases Nat.eq_zero_or_pos (e y.1) with hey | hey
      · rw [hey, pow_zero]; exact Nat.coprime_one_right _
      by_cases hpp : p x.1 = p y.1
      · exfalso
        have hp2 := hsameprime x.1 y.1 hne hex hey hpp
        have hxS : x.1 ∈ S₂ := hS₂mem.mpr ⟨hp2, hex⟩
        have hyS : y.1 ∈ S₂ := hS₂mem.mpr ⟨by rw [← hpp]; exact hp2, hey⟩
        rw [hS₂eq'] at hxS hyS
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxS hyS
        rcases hxS with h | h
        · exact x.2 h
        rcases hyS with h' | h'
        · exact y.2 h'
        exact hne (h.trans h'.symm)
      · exact Nat.Coprime.pow (e x.1) (e y.1)
          ((Nat.coprime_primes (hp _) (hp _)).mpr hpp)
    refine ⟨2, ∏ x : {x : ι // x ≠ i₁}, a x.1, Or.inr rfl, ⟨?_⟩⟩
    have hsplit : (∀ i, ZMod (a i)) ≃+
        ZMod (a i₁) × ∀ x : {x : ι // x ≠ i₁}, ZMod (a x.1) :=
      { Equiv.piSplitAt i₁ (fun i => ZMod (a i)) with
        map_add' := fun f g => rfl }
    have hai₁ : a i₁ = 2 := by
      show p i₁ ^ e i₁ = 2
      rw [hi₁.1, hei₁, pow_one]
    exact eqv.trans (hsplit.trans (AddEquiv.prodCongr
      (ZMod.ringEquivCongr hai₁).toAddEquiv
      (ZMod.prodEquivPi (fun x : {x : ι // x ≠ i₁} => a x.1)
        hcop').toAddEquiv.symm))
  · -- at most one genuinely-even factor: everything is pairwise coprime
    have hcard1 : S₂.card ≤ 1 := by omega
    have hcop : Pairwise (Nat.Coprime on a) := by
      intro i j hij
      show Nat.Coprime (p i ^ e i) (p j ^ e j)
      rcases Nat.eq_zero_or_pos (e i) with hei | hei
      · rw [hei, pow_zero]; exact Nat.coprime_one_left _
      rcases Nat.eq_zero_or_pos (e j) with hej | hej
      · rw [hej, pow_zero]; exact Nat.coprime_one_right _
      by_cases hpp : p i = p j
      · exfalso
        have hp2 := hsameprime i j hij hei hej hpp
        have hiS : i ∈ S₂ := hS₂mem.mpr ⟨hp2, hei⟩
        have hjS : j ∈ S₂ := hS₂mem.mpr ⟨by rw [← hpp]; exact hp2, hej⟩
        have h2 : 1 < S₂.card := Finset.one_lt_card.mpr ⟨i, hiS, j, hjS, hij⟩
        omega
      · exact Nat.Coprime.pow (e i) (e j)
          ((Nat.coprime_primes (hp i) (hp j)).mpr hpp)
    refine ⟨1, ∏ i, a i, Or.inl rfl, ⟨?_⟩⟩
    exact eqv.trans ((ZMod.prodEquivPi a hcop).toAddEquiv.symm.trans
      AddEquiv.uniqueProd.symm)

/-- **The fifteen-groups casework** (PROVEN 2026-07-22): an abelian
group of the shape `ℤ/d × ℤ/n` with `d ∈ {1, 2}`, all of whose element
orders lie in `{1, …, 10, 12}`, and containing no `ℤ/2 × ℤ/10` and no
`ℤ/2 × ℤ/12`, is one of Mazur's fifteen groups. Casework: for `d = 1`
the generator's order pins `n` in the list; for `d = 2` and `n` odd the
group is cyclic of order `2n` by CRT and the generator's order pins
`2n`; for `d = 2` and `n` even the element `(0, 1)` has order `n`, so
`n ∈ {2, 4, 6, 8, 10, 12}`, and the two exclusions remove `10` and
`12`. -/
theorem mazur_group_casework (T : Type*) [AddCommGroup T]
    (horder : ∀ x : T, addOrderOf x ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12} : Finset ℕ))
    (h210 : ∀ φ : (ZMod 2 × ZMod 10) →+ T, ¬ Function.Injective φ)
    (h212 : ∀ φ : (ZMod 2 × ZMod 12) →+ T, ¬ Function.Injective φ)
    (hdec : ∃ (d n : ℕ), (d = 1 ∨ d = 2) ∧ Nonempty (T ≃+ (ZMod d × ZMod n))) :
    (∃ n ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12} : Finset ℕ),
      Nonempty (T ≃+ ZMod n)) ∨
    (∃ m ∈ ({1, 2, 3, 4} : Finset ℕ),
      Nonempty (T ≃+ (ZMod 2 × ZMod (2 * m)))) := by
  classical
  obtain ⟨d, n, hd, ⟨e⟩⟩ := hdec
  rcases hd with rfl | rfl
  · -- `d = 1`: the group is cyclic of order `n`
    left
    have e' : T ≃+ ZMod n := e.trans AddEquiv.uniqueProd
    have hordx : addOrderOf (e'.symm 1) = n := by
      have h1 := addOrderOf_injective e'.toAddMonoidHom e'.injective (e'.symm 1)
      rw [show e'.toAddMonoidHom (e'.symm 1) = 1 from e'.apply_symm_apply 1,
        ZMod.addOrderOf_one] at h1
      exact h1.symm
    have hmem := horder (e'.symm 1)
    rw [hordx] at hmem
    exact ⟨n, hmem, ⟨e'⟩⟩
  · by_cases hpar : 2 ∣ n
    · -- `d = 2`, `n` even: `(0, 1)` has order `n`, and the exclusions apply
      -- the order of `(0, 1)` is `n`
      have hord01 : addOrderOf ((0, 1) : ZMod 2 × ZMod n) = n := by
        have h1 : n • ((0, 1) : ZMod 2 × ZMod n) = 0 := by
          have hz : n • (0 : ZMod 2) = 0 := smul_zero n
          have ho : n • (1 : ZMod n) = 0 := by
            rw [nsmul_eq_mul, mul_one, ZMod.natCast_self]
          rw [Prod.smul_mk, hz, ho]
          rfl
        have hdvd : addOrderOf ((0, 1) : ZMod 2 × ZMod n) ∣ n :=
          addOrderOf_dvd_of_nsmul_eq_zero h1
        have hdvd2 : n ∣ addOrderOf ((0, 1) : ZMod 2 × ZMod n) := by
          have h2 : (addOrderOf ((0, 1) : ZMod 2 × ZMod n)) •
              ((0, 1) : ZMod 2 × ZMod n) = 0 := addOrderOf_nsmul_eq_zero _
          have h3 : (addOrderOf ((0, 1) : ZMod 2 × ZMod n)) • (1 : ZMod n) = 0 :=
            congrArg Prod.snd h2
          have h4 := addOrderOf_dvd_of_nsmul_eq_zero h3
          rwa [ZMod.addOrderOf_one] at h4
        exact Nat.dvd_antisymm hdvd hdvd2
      have hordx : addOrderOf (e.symm ((0, 1) : ZMod 2 × ZMod n)) = n := by
        have h1 := addOrderOf_injective e.toAddMonoidHom e.injective (e.symm (0, 1))
        rw [show e.toAddMonoidHom (e.symm (0, 1)) = (0, 1) from e.apply_symm_apply _,
          hord01] at h1
        exact h1.symm
      have hmem := horder (e.symm ((0, 1) : ZMod 2 × ZMod n))
      rw [hordx] at hmem
      fin_cases hmem
      · exact absurd hpar (by norm_num)
      · exact Or.inr ⟨1, by decide, ⟨e⟩⟩
      · exact absurd hpar (by norm_num)
      · exact Or.inr ⟨2, by decide, ⟨e⟩⟩
      · exact absurd hpar (by norm_num)
      · exact Or.inr ⟨3, by decide, ⟨e⟩⟩
      · exact absurd hpar (by norm_num)
      · exact Or.inr ⟨4, by decide, ⟨e⟩⟩
      · exact absurd hpar (by norm_num)
      · exact absurd e.symm.injective (h210 e.symm.toAddMonoidHom)
      · exact absurd e.symm.injective (h212 e.symm.toAddMonoidHom)
    · -- `d = 2`, `n` odd: the group is cyclic of order `2n` by CRT
      left
      have hcop : Nat.Coprime 2 n := (Nat.prime_two.coprime_iff_not_dvd).mpr hpar
      have e' : T ≃+ ZMod (2 * n) :=
        e.trans ((ZMod.chineseRemainder hcop).toAddEquiv).symm
      have hordx : addOrderOf (e'.symm 1) = 2 * n := by
        have h1 := addOrderOf_injective e'.toAddMonoidHom e'.injective (e'.symm 1)
        rw [show e'.toAddMonoidHom (e'.symm 1) = 1 from e'.apply_symm_apply 1,
          ZMod.addOrderOf_one] at h1
        exact h1.symm
      have hmem := horder (e'.symm 1)
      rw [hordx] at hmem
      exact ⟨2 * n, hmem, ⟨e'⟩⟩

/-- **Mazur's torsion theorem** (DERIVED 2026-07-22 from the five
arithmetic leaves, the PROVEN `(ℤ/2)³` bound, the group-theoretic
rank-`≤2` leaf, and the PROVEN casework): the torsion subgroup of the
rational points of an elliptic curve over `ℚ` is isomorphic to one of
the fifteen groups `ℤ/n` with `n ∈ {1, …, 10, 12}` or `ℤ/2 × ℤ/2m` with
`m ∈ {1, 2, 3, 4}`. Mazur, "Modular curves and the Eisenstein ideal"
(Publ. Math. IHÉS 47, 1977) and "Rational isogenies of prime degree"
(Invent. Math. 44, 1978). -/
theorem WeierstrassCurve.mazur_classification (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (∃ n ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12} : Finset ℕ),
      Nonempty ((Submodule.torsion ℤ (E⁄ℚ).Point) ≃+ ZMod n)) ∨
    (∃ m ∈ ({1, 2, 3, 4} : Finset ℕ),
      Nonempty ((Submodule.torsion ℤ (E⁄ℚ).Point) ≃+ (ZMod 2 × ZMod (2 * m)))) := by
  haveI : Finite (Submodule.torsion ℤ (E⁄ℚ).Point) := E.torsion_finite_rat
  have hιinj : Function.Injective
      ((Submodule.torsion ℤ (E⁄ℚ).Point).subtype.toAddMonoidHom) :=
    Submodule.injective_subtype _
  refine mazur_group_casework (Submodule.torsion ℤ (E⁄ℚ).Point) ?_ ?_ ?_ ?_
  · -- element orders through Mazur's uniform bound
    intro x
    have h1 := addOrderOf_injective
      ((Submodule.torsion ℤ (E⁄ℚ).Point).subtype.toAddMonoidHom) hιinj x
    rw [← h1]
    exact E.mazur_point_order _ x.2
  · -- no `ℤ/2 × ℤ/10`
    intro φ hφ
    exact E.not_two_ten_torsion
      (((Submodule.torsion ℤ (E⁄ℚ).Point).subtype.toAddMonoidHom).comp φ)
      (hιinj.comp hφ)
  · -- no `ℤ/2 × ℤ/12`
    intro φ hφ
    exact E.not_two_twelve_torsion
      (((Submodule.torsion ℤ (E⁄ℚ).Point).subtype.toAddMonoidHom).comp φ)
      (hιinj.comp hφ)
  · -- the rank-`≤2` shape, from the Weil-pairing leaf and the `2`-torsion bound
    refine AddCommGroup.exists_rank_le_two_decomposition _ ?_ ?_
    · intro n hn φ hφ
      exact E.not_full_torsion_rat hn
        (((Submodule.torsion ℤ (E⁄ℚ).Point).subtype.toAddMonoidHom).comp φ)
        (hιinj.comp hφ)
    · intro φ hφ
      exact E.not_two_cube_torsion
        (((Submodule.torsion ℤ (E⁄ℚ).Point).subtype.toAddMonoidHom).comp φ)
        (hιinj.comp hφ)

/-- **Mazur's torsion theorem, weak form**: the rational points of an
elliptic curve over `ℚ` contain no subgroup isomorphic to `ℤ/2 × ℤ/2p` for
any `p ≥ 5` (primality is not needed: the order comparison `4p ≥ 20 > 16`
alone suffices) — equivalently, no additive homomorphism
`ℤ/2 × ℤ/2p →+ E(ℚ)` is injective. Derived from `mazur_classification`:
the image consists of torsion points, so the homomorphism corestricts to an
injection into the torsion subgroup, which by the classification is finite
of order at most `16 < 4p`. -/
theorem WeierstrassCurve.mazur_torsion_bound (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {p : ℕ} (h5 : 5 ≤ p)
    (φ : (ZMod 2 × ZMod (2 * p)) →+ (E⁄ℚ).Point) :
    ¬ Function.Injective φ := by
  intro hφ
  haveI : NeZero (2 * p) := ⟨by omega⟩
  -- every image point is torsion: `x` has finite additive order in the
  -- finite group `ℤ/2 × ℤ/2p`, and `φ` transports the annihilation
  have hmem : ∀ x : ZMod 2 × ZMod (2 * p),
      φ x ∈ Submodule.torsion ℤ (E⁄ℚ).Point := by
    intro x
    rw [Submodule.mem_torsion_iff]
    refine ⟨⟨(addOrderOf x : ℤ),
      mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast (addOrderOf_pos x).ne')⟩, ?_⟩
    show (addOrderOf x : ℤ) • φ x = 0
    rw [natCast_zsmul, ← map_nsmul, addOrderOf_nsmul_eq_zero, map_zero]
  -- corestrict to the torsion subgroup, preserving injectivity
  let φ' : (ZMod 2 × ZMod (2 * p)) →+ (Submodule.torsion ℤ (E⁄ℚ).Point) :=
    φ.codRestrict (Submodule.torsion ℤ (E⁄ℚ).Point) hmem
  have hφ' : Function.Injective φ' := fun a b hab => hφ (Subtype.ext_iff.mp hab)
  -- compare cardinalities against the fifteen groups
  rcases E.mazur_classification with ⟨n, hn, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩
  · have hn12 : 1 ≤ n ∧ n ≤ 12 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      omega
    haveI : NeZero n := ⟨by omega⟩
    haveI : Finite (Submodule.torsion ℤ (E⁄ℚ).Point) :=
      Finite.of_equiv (ZMod n) e.symm.toEquiv
    have hcard := Nat.card_le_card_of_injective φ' hφ'
    rw [Nat.card_prod, Nat.card_zmod, Nat.card_zmod,
      Nat.card_congr e.toEquiv, Nat.card_zmod] at hcard
    omega
  · have hm4 : 1 ≤ m ∧ m ≤ 4 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      omega
    haveI : NeZero (2 * m) := ⟨by omega⟩
    haveI : Finite (Submodule.torsion ℤ (E⁄ℚ).Point) :=
      Finite.of_equiv (ZMod 2 × ZMod (2 * m)) e.symm.toEquiv
    have hcard := Nat.card_le_card_of_injective φ' hφ'
    rw [Nat.card_prod, Nat.card_zmod, Nat.card_zmod, Nat.card_congr e.toEquiv,
      Nat.card_prod, Nat.card_zmod, Nat.card_zmod] at hcard
    omega

-- `asIdeal_toHeightOneSpectrumRingOfIntegersRat` and
-- `maximalIdeal_adicCompletionIntegers_eq_span` were hoisted (2026-07-25)
-- to `Fermat/FLT/Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean`,
-- the shim where `toHeightOneSpectrumRingOfIntegersRat` itself is defined,
-- so that `GroupScheme/ConnectedEtale.lean` — far UPSTREAM of this file —
-- can use them instead of re-deriving them locally. The names and
-- statements are unchanged, so use sites here and downstream are unaffected.

set_option backward.isDefEq.respectTransparency false in
/-- **Minkowski surjectivity transport** (DERIVED 2026-07-16 from the
local inertia-fixed-field node
`maximalIdeal_map_eq_of_le_fixedField_localInertiaGroup`): if the image
in `G_ℚ` of the local inertia group at `q` fixes the finite Galois
extension `L/ℚ` pointwise, then SOME prime `Q₀` of `𝓞 L` above `q` has
trivial ideal-inertia in `Gal(L/ℚ)`. Construction: the chosen embedding
`ι : ℚᵃˡᵍ → (ℚ_q)ᵃˡᵍ` (the one underlying `absoluteGaloisGroup.map`)
carries `L` into the finite subextension `M := ℚ_q(ι(L))`, which the
hypothesis and `lift_map` place inside the fixed field of the local
inertia; the local node then makes `q` a uniformizer of the integral
closure `𝒪_M`. Pulling the maximal ideal of `𝒪_M` back along
`ι : 𝓞 L → 𝒪_M` yields a prime `Q₀ ∋ q` with `e(Q₀|q) = 1` (if `e ≥ 2`
then `q ∈ Q₀²`, so `q ∈ 𝔪_M² = (q²)`, making `q` a unit of `𝒪_M` —
absurd), and `#I(Q₀) = e = 1` closes by
`card_inertia_eq_ramificationIdxIn`. No decomposition-group theory or
henselian lifting is used. -/
theorem exists_prime_over_inertia_eq_bot_of_le_fixingSubgroup
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L]
    [NumberField L] [IsGalois ℚ L]
    {q : ℕ} (hq : q.Prime)
    (hle : Subgroup.map (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom
        (localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat)
      ≤ L.fixingSubgroup) :
    ∃ (Q₀ : Ideal (NumberField.RingOfIntegers L)) (_ : Q₀.IsPrime)
      (_ : (q : NumberField.RingOfIntegers L) ∈ Q₀),
      Q₀.inertia (L ≃ₐ[ℚ] L) = ⊥ := by
  classical
  -- the chosen embedding of algebraic closures underlying the map of
  -- absolute Galois groups
  set f : ℚ →+* IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat :=
    algebraMap ℚ _
  set ι : AlgebraicClosure ℚ →+* AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) :=
    AlgebraicClosure.map f
  -- a finite generating set for `L/ℚ`
  obtain ⟨s, hs⟩ := L.fg_iff_finiteType.mpr (inferInstanceAs (Algebra.FiniteType ℚ L))
  have hL : L = IntermediateField.adjoin ℚ ↑s :=
    IntermediateField.eq_adjoin_of_eq_algebra_adjoin _ _ _ hs.symm
  -- the image field `M := ℚ_q(ι(s)) = ℚ_q(ι(L))`
  set M : IntermediateField
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) :=
    IntermediateField.adjoin _ (ι '' ↑s) with hM
  -- `ι` carries all of `L` into `M`
  have hsub : ∀ x ∈ L, ι x ∈ M := by
    intro x hx
    rw [hL] at hx
    induction hx using IntermediateField.adjoin_induction with
    | mem y hy => exact IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩
    | algebraMap c =>
        rw [AlgebraicClosure.map_algebraMap]
        exact M.algebraMap_mem _
    | add x y hx hy ihx ihy => rw [map_add]; exact add_mem ihx ihy
    | inv x hx ihx => rw [map_inv₀]; exact inv_mem ihx
    | mul x y hx hy ihx ihy => rw [map_mul]; exact mul_mem ihx ihy
  -- `M/ℚ_q` is finite: it is generated by the finite set `ι '' s` of
  -- integral (= algebraic) elements
  haveI hfdM : FiniteDimensional
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) M := by
    haveI : Finite (ι '' (↑s : Set (AlgebraicClosure ℚ))) :=
      (s.finite_toSet.image ι).to_subtype
    exact IntermediateField.finiteDimensional_adjoin
      fun x _ => Algebra.IsIntegral.isIntegral x
  -- the hypothesis places `M` inside the fixed field of the local inertia
  have hMfix : M ≤ IntermediateField.fixedField
      (localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat) := by
    rw [hM, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    -- `σ (ι y) = ι ((map f σ) y) = ι y` by `lift_map` and the hypothesis
    have hmem : (Field.absoluteGaloisGroup.map f) σ ∈ L.fixingSubgroup :=
      hle (Subgroup.mem_map_of_mem _ hσ)
    have hfixy : (Field.absoluteGaloisGroup.map f σ) y = y :=
      (IntermediateField.mem_fixingSubgroup_iff L ((Field.absoluteGaloisGroup.map f) σ)).mp
        hmem y (hL ▸ IntermediateField.subset_adjoin _ _ hy)
    calc σ (ι y) = ι ((Field.absoluteGaloisGroup.map f σ) y) :=
          (Field.absoluteGaloisGroup.lift_map f σ y).symm
      _ = ι y := by rw [hfixy]
  -- the local node: `q` generates the maximal ideal of `𝒪_M`
  have hmax := maximalIdeal_map_eq_of_le_fixedField_localInertiaGroup
    hq.toHeightOneSpectrumRingOfIntegersRat M hMfix
  have hspan : IsLocalRing.maximalIdeal
      (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) M) =
      Ideal.span {(q : IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat) M)} := by
    rw [← hmax, maximalIdeal_adicCompletionIntegers_eq_span hq, Ideal.map_span,
      Set.image_singleton, map_natCast]
  -- the ring homomorphism `ψ : L → M` induced by `ι`
  let ψ : L →+* M :=
    { toFun := fun y => ⟨ι (y : AlgebraicClosure ℚ), hsub _ y.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp
      map_zero' := by
        apply Subtype.ext
        simp
      map_add' := fun a b => by
        apply Subtype.ext
        simp }
  -- `ψ` carries the ring of integers of `L` into `𝒪_M`
  have hψint : ∀ x : NumberField.RingOfIntegers L,
      ψ (algebraMap (NumberField.RingOfIntegers L) L x) ∈
        integralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat) M := by
    intro x
    have h1 : IsIntegral ℤ (algebraMap (NumberField.RingOfIntegers L) L x) :=
      NumberField.RingOfIntegers.isIntegral_coe x
    -- promote `ψ` to a `ℤ`-algebra homomorphism with the AMBIENT `ℤ`-algebra
    -- structures (all ring homs from `ℤ` agree, so `commutes'` is by
    -- uniqueness of `ℤ →+* ·`)
    let ψℤ : L →ₐ[ℤ] M :=
      { toRingHom := ψ
        commutes' := fun n => by
          rw [RingHom.eq_intCast' (algebraMap ℤ L), RingHom.eq_intCast' (algebraMap ℤ M)]
          exact map_intCast ψ n }
    have h2 : IsIntegral ℤ (ψ (algebraMap (NumberField.RingOfIntegers L) L x)) :=
      h1.map ψℤ
    -- pass from `ℤ`-integrality to `𝒪ᵥ`-integrality by pushing the monic
    -- witness through `ℤ → 𝒪ᵥ` (instance-agnostic: all ring homs from `ℤ`
    -- agree)
    obtain ⟨p, hp, hpeval⟩ := h2
    refine ⟨p.map (Int.castRingHom
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, Subsingleton.elim
      ((algebraMap
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat) M).comp
        (Int.castRingHom
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)))
      (algebraMap ℤ M)]
    exact hpeval
  let φ : NumberField.RingOfIntegers L →+*
      IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) M :=
    (ψ.comp (algebraMap (NumberField.RingOfIntegers L) L)).codRestrict
      (integralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) M) hψint
  -- the embedding prime: the pullback of the maximal ideal of `𝒪_M`
  haveI hmaxprime : (IsLocalRing.maximalIdeal
      (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) M)).IsPrime :=
    (IsLocalRing.maximalIdeal.isMaximal _).isPrime
  refine ⟨Ideal.comap φ (IsLocalRing.maximalIdeal _), Ideal.IsPrime.comap φ, ?_, ?_⟩
  · -- `q` lands in the pullback: `φ q = q ∈ 𝔪_M = (q)`
    rw [Ideal.mem_comap, map_natCast, hspan]
    exact Ideal.mem_span_singleton_self _
  -- inertia is trivial: `#I(Q₀) = e(Q₀|q) = 1`
  have hQ₀mem : (q : NumberField.RingOfIntegers L) ∈
      Ideal.comap φ (IsLocalRing.maximalIdeal _) := by
    rw [Ideal.mem_comap, map_natCast, hspan]
    exact Ideal.mem_span_singleton_self _
  haveI hQ₀prime : (Ideal.comap φ (IsLocalRing.maximalIdeal _)).IsPrime :=
    Ideal.IsPrime.comap φ
  -- instance pack for `card_inertia_eq_ramificationIdxIn` (mirrors the
  -- inertia dictionary proof below)
  haveI := IsIntegralClosure.isIntegral_algebra ℤ (A := NumberField.RingOfIntegers L) L
  have hqZ : Prime ((q : ℤ)) := Nat.prime_iff_prime_int.mp hq
  haveI hsp : (Ideal.span {((q : ℤ))} : Ideal ℤ).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr hqZ
  have hne : (Ideal.span {((q : ℤ))} : Ideal ℤ) ≠ ⊥ := by
    simp only [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  haveI hlies : (Ideal.comap φ (IsLocalRing.maximalIdeal _)).LiesOver
      (Ideal.span {((q : ℤ))}) :=
    (Ideal.liesOver_span_iff hQ₀prime.ne_top hqZ).mpr (by exact_mod_cast hQ₀mem)
  haveI hfinq : Finite (ℤ ⧸ (Ideal.span {((q : ℤ))} : Ideal ℤ)) :=
    Ring.HasFiniteQuotients.finiteQuotient hne
  haveI hmaxZ : (Ideal.span {((q : ℤ))} : Ideal ℤ).IsMaximal :=
    hsp.isMaximal_of_ne_bot hne
  have hsurjZ : Function.Surjective
      (algebraMap (ℤ ⧸ (Ideal.span {((q : ℤ))} : Ideal ℤ))
        ((Ideal.span {((q : ℤ))} : Ideal ℤ).ResidueField)) :=
    IsFractionRing.surjective_iff_isField.mpr
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmaxZ)
  haveI : Finite ((Ideal.span {((q : ℤ))} : Ideal ℤ).ResidueField) :=
    Finite.of_surjective _ hsurjZ
  -- the ramification index (old spelling) is `1`
  have hple : Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
      (Ideal.span {((q : ℤ))}) ≤ Ideal.comap φ (IsLocalRing.maximalIdeal _) := by
    rw [Ideal.map_span, Set.image_singleton]
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact_mod_cast hQ₀mem
  have he1 : Ideal.ramificationIdx' (Ideal.span {((q : ℤ))})
      (Ideal.comap φ (IsLocalRing.maximalIdeal _)) = 1 := by
    by_contra hne1
    have hsq := (Ideal.ramificationIdx'_ne_one_iff hple).mp hne1
    -- then `q ∈ Q₀²`, so `φ q = q ∈ 𝔪_M² = (q²)`, making `q` a unit
    have hqQ2 : (q : NumberField.RingOfIntegers L) ∈
        (Ideal.comap φ (IsLocalRing.maximalIdeal _)) ^ 2 := by
      refine hsq ?_
      have : algebraMap ℤ (NumberField.RingOfIntegers L) (q : ℤ) ∈
          Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
            (Ideal.span {((q : ℤ))}) :=
        Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)
      simpa using this
    have hcomap2 : (Ideal.comap φ (IsLocalRing.maximalIdeal _)) ^ 2 ≤
        Ideal.comap φ ((IsLocalRing.maximalIdeal _) ^ 2) := by
      rw [pow_two, pow_two]
      exact Ideal.mul_le.mpr fun r hr t ht => Ideal.mem_comap.mpr
        (by rw [map_mul]; exact Ideal.mul_mem_mul hr ht)
    have hφq := Ideal.mem_comap.mp (hcomap2 hqQ2)
    rw [map_natCast, hspan, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hφq
    obtain ⟨c, hc⟩ := hφq
    -- `q ≠ 0` in `𝒪_M` (its image in `(ℚ_q)ᵃˡᵍ` is `q ≠ 0` by char zero)
    haveI : CharZero (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)) :=
      charZero_of_injective_algebraMap (algebraMap
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat) _).injective
    have hq0 : ((q : IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat) M)) ≠ 0 := by
      intro h0
      have h1 := congrArg (fun z => (algebraMap M (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))
        ((algebraMap (IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat) M) M) z))) h0
      simp only [map_natCast, map_zero] at h1
      exact Nat.cast_ne_zero.mpr hq.ne_zero h1
    -- cancel one factor of `q`: `q · c = 1`
    have hcancel : (q : IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat) M) * c = 1 := by
      have hmul : (q : IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat) M) *
          ((q : IntegralClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat) M) * c) =
          (q : IntegralClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat) M) * 1 := by
        rw [mul_one, ← mul_assoc, ← pow_two]
        exact hc.symm
      exact mul_left_cancel₀ hq0 hmul
    -- but `q` lies in the proper maximal ideal — contradiction
    have hqmem : (q : IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat) M) ∈
        IsLocalRing.maximalIdeal _ := by
      rw [hspan]; exact Ideal.mem_span_singleton_self _
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      (Ideal.eq_top_of_isUnit_mem _ hqmem
        (isUnit_iff_exists.mpr ⟨c, hcancel, by rwa [mul_comm] at hcancel⟩))
  -- bridge to the `Module.length` spelling and conclude via
  -- `#I(Q₀) = e = 1`
  have h2 : (Ideal.comap φ (IsLocalRing.maximalIdeal _)).ramificationIdx ℤ = 1 := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {((q : ℤ))})
      (Ideal.comap φ (IsLocalRing.maximalIdeal _)) hne]
    exact he1
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn
    (G := (L ≃ₐ[ℚ] L)) (Ideal.span {((q : ℤ))})
    (Ideal.comap φ (IsLocalRing.maximalIdeal _))
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {((q : ℤ))})
    (Ideal.comap φ (IsLocalRing.maximalIdeal _)) (L ≃ₐ[ℚ] L), h2] at hcard
  exact Subgroup.eq_bot_of_card_eq _ hcard

set_option backward.isDefEq.respectTransparency false in
/-- **Conjugacy propagation of trivial inertia** (PROVEN 2026-07-16): if ONE
prime of `𝓞 L` above `q` has trivial ideal-inertia in `Gal(L/ℚ)`, then
EVERY prime above `q` does. Classical: `Gal(L/ℚ)` acts transitively on
the primes above `q` (`Ideal.IsInvariant.orbit_eq_primesOver` /
going-up), and inertia groups at conjugate primes are conjugate
(`I(g • Q) = g I(Q) g⁻¹`), so triviality propagates along the orbit. -/
theorem inertia_eq_bot_of_exists_prime_over
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L]
    [NumberField L] [IsGalois ℚ L]
    {q : ℕ} (hq : q.Prime)
    (Q₀ : Ideal (NumberField.RingOfIntegers L)) [Q₀.IsPrime]
    (hQ₀mem : (q : NumberField.RingOfIntegers L) ∈ Q₀)
    (hQ₀ : Q₀.inertia (L ≃ₐ[ℚ] L) = ⊥)
    (Q : Ideal (NumberField.RingOfIntegers L)) [Q.IsPrime]
    (hQmem : (q : NumberField.RingOfIntegers L) ∈ Q) :
    Q.inertia (L ≃ₐ[ℚ] L) = ⊥ := by
  haveI := IsIntegralClosure.isIntegral_algebra ℤ (A := NumberField.RingOfIntegers L) L
  have hqZ : Prime ((q : ℤ)) := Nat.prime_iff_prime_int.mp hq
  haveI hsp : (Ideal.span {((q : ℤ))} : Ideal ℤ).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr hqZ
  have hne : (Ideal.span {((q : ℤ))} : Ideal ℤ) ≠ ⊥ := by
    simp only [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  haveI hmax : (Ideal.span {((q : ℤ))} : Ideal ℤ).IsMaximal :=
    hsp.isMaximal_of_ne_bot hne
  haveI hlies₀ : Q₀.LiesOver (Ideal.span {((q : ℤ))}) :=
    (Ideal.liesOver_span_iff (Ideal.IsPrime.ne_top ‹Q₀.IsPrime›) hqZ).mpr
      (by exact_mod_cast hQ₀mem)
  haveI hlies : Q.LiesOver (Ideal.span {((q : ℤ))}) :=
    (Ideal.liesOver_span_iff (Ideal.IsPrime.ne_top ‹Q.IsPrime›) hqZ).mpr
      (by exact_mod_cast hQmem)
  haveI := IsGaloisGroup.of_isFractionRing (L ≃ₐ[ℚ] L) ℤ
    (NumberField.RingOfIntegers L) ℚ L
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
    (Ideal.span {((q : ℤ))}) Q₀ Q ((L ≃ₐ[ℚ] L))
  rw [← hσ]
  rw [Subgroup.eq_bot_iff_forall] at hQ₀ ⊢
  intro g hg
  have hconj : σ⁻¹ * g * σ ∈ Q₀.inertia (L ≃ₐ[ℚ] L) := by
    intro y
    have h1 := hg (σ • y)
    rw [Submodule.mem_toAddSubgroup,
      Ideal.mem_pointwise_smul_iff_inv_smul_mem] at h1
    rw [Submodule.mem_toAddSubgroup]
    have h2 : σ⁻¹ • (g • σ • y - σ • y) = (σ⁻¹ * g * σ) • y - y := by
      rw [smul_sub, inv_smul_smul, ← mul_smul, ← mul_smul]
    rwa [h2] at h1
  have h3 : σ⁻¹ * g * σ = 1 := hQ₀ _ hconj
  have h4 : g = σ * (σ⁻¹ * g * σ) * σ⁻¹ := by group
  rw [h4, h3, mul_one, mul_inv_cancel]

/-- **The inertia transport** (DERIVED 2026-07-16 from the two nodes
above): the image of `localInertiaGroup q` fixing `L` pointwise
trivializes the global ideal-inertia at EVERY prime above `q` — the
embedding-determined prime has trivial inertia by the surjectivity
node, and conjugacy propagates it. -/
theorem inertia_eq_bot_of_le_fixingSubgroup
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L]
    [NumberField L] [IsGalois ℚ L]
    {q : ℕ} (hq : q.Prime)
    (hle : Subgroup.map (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom
        (localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat)
      ≤ L.fixingSubgroup)
    (Q : Ideal (NumberField.RingOfIntegers L)) [Q.IsPrime]
    (hQmem : (q : NumberField.RingOfIntegers L) ∈ Q) :
    Q.inertia (L ≃ₐ[ℚ] L) = ⊥ := by
  obtain ⟨Q₀, hQ₀p, hQ₀mem, hQ₀⟩ :=
    exists_prime_over_inertia_eq_bot_of_le_fixingSubgroup L hq hle
  exact inertia_eq_bot_of_exists_prime_over L hq Q₀ hQ₀mem hQ₀ Q hQmem

set_option backward.isDefEq.respectTransparency false in
/-- **The inertia dictionary** (DERIVED 2026-07-16 from the transport
node above): if the image in `G_ℚ` of the local inertia group at `q`
fixes the finite Galois extension `L/ℚ` pointwise, then every prime of
`𝓞 L` above `q` is unramified over `ℤ`. Chain: the transport node
trivializes the global ideal-inertia `Q.inertia Gal(L/ℚ)`; its
cardinality IS the ramification index
(`card_inertia_eq_ramificationIdxIn`); `ramificationIdxIn` transfers to
the specific prime; and `ramificationIdx_eq_one_iff` converts `e = 1`
to `Algebra.IsUnramifiedAt` (the `PerfectField` side condition comes
from finiteness of the residue field, via the fraction-ring bridge and
`maximal_ideal_iff_isField_quotient`). -/
theorem isUnramifiedAt_of_inertia_le_fixingSubgroup
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L]
    [NumberField L] [IsGalois ℚ L]
    {q : ℕ} (hq : q.Prime)
    (hle : Subgroup.map (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom
        (localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat)
      ≤ L.fixingSubgroup)
    (Q : Ideal (NumberField.RingOfIntegers L)) [Q.IsPrime]
    (hQmem : (q : NumberField.RingOfIntegers L) ∈ Q) :
    Algebra.IsUnramifiedAt ℤ Q := by
  haveI := IsIntegralClosure.isIntegral_algebra ℤ (A := NumberField.RingOfIntegers L) L
  have hqZ : Prime ((q : ℤ)) := Nat.prime_iff_prime_int.mp hq
  haveI hsp : (Ideal.span {((q : ℤ))} : Ideal ℤ).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr hqZ
  have hne : (Ideal.span {((q : ℤ))} : Ideal ℤ) ≠ ⊥ := by
    simp only [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  haveI hlies : Q.LiesOver (Ideal.span {((q : ℤ))}) :=
    (Ideal.liesOver_span_iff (Ideal.IsPrime.ne_top ‹Q.IsPrime›) hqZ).mpr
      (by exact_mod_cast hQmem)
  haveI hfinq : Finite (ℤ ⧸ (Ideal.span {((q : ℤ))} : Ideal ℤ)) :=
    Ring.HasFiniteQuotients.finiteQuotient hne
  haveI hmax : (Ideal.span {((q : ℤ))} : Ideal ℤ).IsMaximal :=
    hsp.isMaximal_of_ne_bot hne
  have hsurj : Function.Surjective
      (algebraMap (ℤ ⧸ (Ideal.span {((q : ℤ))} : Ideal ℤ))
        ((Ideal.span {((q : ℤ))} : Ideal ℤ).ResidueField)) :=
    IsFractionRing.surjective_iff_isField.mpr
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax)
  haveI : Finite ((Ideal.span {((q : ℤ))} : Ideal ℤ).ResidueField) :=
    Finite.of_surjective _ hsurj
  -- `e = |inertia| = |⊥| = 1`
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn
    (G := (L ≃ₐ[ℚ] L)) (Ideal.span {((q : ℤ))}) Q
  rw [inertia_eq_bot_of_le_fixingSubgroup L hq hle Q hQmem] at hcard
  have h1 : Ideal.ramificationIdxIn (Ideal.span {((q : ℤ))})
      (NumberField.RingOfIntegers L) = 1 := by
    rw [← hcard]
    simp
  have h2 : Q.ramificationIdx ℤ = 1 := by
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx
      (Ideal.span {((q : ℤ))}) Q (L ≃ₐ[ℚ] L)]
    exact h1
  exact Ideal.ramificationIdx_eq_one_iff.mp h2

set_option backward.isDefEq.respectTransparency false in
/-- **Minkowski, subgroup form** (DERIVED 2026-07-16 from the inertia
dictionary and mathlib's discriminant theory): an open normal subgroup
of `G_ℚ` containing the image of the local inertia group at every prime
is everything. Assembly: the fixed field `L` of `H` recovers `H` by the
infinite Galois correspondence (`H` is closed since open); `L` is a
finite Galois number field (`isOpen_iff_finite`, `normal_iff_isGalois`);
if `H ≠ ⊤` then `L ≠ ⊥` so `1 < finrank ℚ L`, and
`exists_not_isUnramifiedAt_int_of_isGalois` produces a prime `p` all of
whose primes in `𝓞 L` are ramified; but the inertia hypothesis plus the
dictionary make the lifted prime above `p` unramified — contradiction. -/
theorem open_normal_subgroup_eq_top_of_inertia_le
    (H : Subgroup (Field.absoluteGaloisGroup ℚ)) [hnorm : H.Normal]
    (hopen : IsOpen (H : Set (Field.absoluteGaloisGroup ℚ)))
    (hinertia : ∀ (q : ℕ) (hq : q.Prime),
      Subgroup.map (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom
        (localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat) ≤ H) :
    H = ⊤ := by
  haveI hgal : IsGalois ℚ (AlgebraicClosure ℚ) := inferInstance
  by_contra hne
  have hclosed : IsClosed (H : Set (Field.absoluteGaloisGroup ℚ)) :=
    Subgroup.isClosed_of_isOpen H hopen
  set L : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.fixedField (E := AlgebraicClosure ℚ) H
  have hfix : L.fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, hclosed⟩
  haveI hfd : FiniteDimensional ℚ L :=
    (InfiniteGalois.isOpen_iff_finite L).mp (by rw [hfix]; exact hopen)
  haveI hgalL : IsGalois ℚ L := (InfiniteGalois.normal_iff_isGalois L).mp
    (by rw [hfix]; exact hnorm)
  haveI : NumberField L := ⟨⟩
  have hrank : 1 < Module.finrank ℚ L := by
    rcases Nat.lt_or_ge 1 (Module.finrank ℚ L) with h | h
    · exact h
    · exfalso
      have h0 : 0 < Module.finrank ℚ L := Module.finrank_pos
      have h1 : Module.finrank ℚ L = 1 := by omega
      apply hne
      rw [← hfix, IntermediateField.finrank_eq_one_iff.mp h1,
        IntermediateField.fixingSubgroup_bot]
  obtain ⟨p, hp, hram⟩ := NumberField.exists_not_isUnramifiedAt_int_of_isGalois
    (K := L) (𝒪 := NumberField.RingOfIntegers L) hrank
  -- lift `p` to a prime of `𝓞 L`
  haveI := IsIntegralClosure.isIntegral_algebra ℤ (A := NumberField.RingOfIntegers L) L
  have hpZ : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.mp hp
  haveI hPspan : (Ideal.span {((p : ℤ))} : Ideal ℤ).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr hpZ
  have hker : RingHom.ker (algebraMap ℤ (NumberField.RingOfIntegers L)) ≤
      Ideal.span {((p : ℤ))} := by
    intro x hx
    have hx0 : algebraMap ℤ (NumberField.RingOfIntegers L) x = 0 := hx
    have hxL : algebraMap ℤ L x = 0 := by
      rw [IsScalarTower.algebraMap_eq ℤ (NumberField.RingOfIntegers L) L, RingHom.comp_apply,
        hx0, map_zero]
    have : (x : ℤ) = 0 := by
      have := congrArg (fun y => y) hxL
      exact_mod_cast (by simpa using hxL : ((x : ℤ) : L) = 0)
    rw [this]
    exact Ideal.zero_mem _
  obtain ⟨Q, hQprime, hQcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
      (S := NumberField.RingOfIntegers L) (Ideal.span {((p : ℤ))}) hker
  haveI := hQprime
  have hpQ : ((p : ℕ) : NumberField.RingOfIntegers L) ∈ Q := by
    have hmem : ((p : ℤ)) ∈ Ideal.span {((p : ℤ))} :=
      Ideal.subset_span rfl
    rw [← hQcomap] at hmem
    have := Ideal.mem_comap.mp hmem
    simpa using this
  exact hram Q hQprime hpQ
    (isUnramifiedAt_of_inertia_le_fixingSubgroup L hp
      (le_trans (hinertia p hp) (le_of_eq hfix.symm)) Q hpQ)

/-- **Minkowski for mod-`p` characters** (DERIVED 2026-07-16 from the
subgroup form): a character `χ : G_ℚ → (ℤ/p)ˣ` with open kernel that is
unramified at every finite place (the local inertia group at every
prime `q` is killed by the restriction of `χ` to `G_{ℚ_q}`) is trivial.
The kernel is an open normal subgroup containing every inertia image,
hence everything. -/
theorem minkowski_character_trivial {T : Type*} [Group T]
    (χ : Field.absoluteGaloisGroup ℚ →* T)
    (hker : IsOpen (χ.ker : Set (Field.absoluteGaloisGroup ℚ)))
    (hunram : ∀ (q : ℕ) (hq : q.Prime),
      localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat ≤
        (χ.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker) :
    χ = 1 := by
  have hker_top : χ.ker = ⊤ := by
    refine open_normal_subgroup_eq_top_of_inertia_le χ.ker hker ?_
    intro q hq
    rw [Subgroup.map_le_iff_le_comap]
    intro σ hσ
    have h := hunram q hq hσ
    rw [MonoidHom.mem_ker] at h
    rw [Subgroup.mem_comap, MonoidHom.mem_ker]
    exact h
  ext g
  have hg : g ∈ χ.ker := hker_top ▸ Subgroup.mem_top g
  simpa [MonoidHom.mem_ker] using hg

set_option backward.isDefEq.respectTransparency false in
/-- **Galois descent for points** (PROVEN 2026-07-17): a point of
`E(ℚ̄)` fixed by every element of the absolute Galois group is the base
change of a rational point. The coordinates are fixed by all
automorphisms of the Galois extension `ℚ̄/ℚ`, hence lie in `ℚ`
(`InfiniteGalois.mem_range_algebraMap_iff_fixed`), and nonsingularity
descends along the injective base change
(`baseChange_nonsingular`). -/
theorem WeierstrassCurve.exists_point_eq_baseChange_of_fixed
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Pt : (E⁄(AlgebraicClosure ℚ)).Point)
    (hfix : ∀ σ : Field.absoluteGaloisGroup ℚ,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom Pt = Pt) :
    ∃ Q : (E⁄ℚ).Point,
      Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) Q = Pt := by
  cases Pt with
  | zero => exact ⟨0, rfl⟩
  | some x y h =>
    have hx : x ∈ Set.range (algebraMap ℚ (AlgebraicClosure ℚ)) := by
      refine (InfiniteGalois.mem_range_algebraMap_iff_fixed x).mpr fun σ => ?_
      have h1 := hfix σ
      rw [Affine.Point.map_some] at h1
      exact (Affine.Point.some.inj h1).left
    have hy : y ∈ Set.range (algebraMap ℚ (AlgebraicClosure ℚ)) := by
      refine (InfiniteGalois.mem_range_algebraMap_iff_fixed y).mpr fun σ => ?_
      have h1 := hfix σ
      rw [Affine.Point.map_some] at h1
      exact (Affine.Point.some.inj h1).right
    obtain ⟨x₀, hx₀⟩ := hx
    obtain ⟨y₀, hy₀⟩ := hy
    have h₀ : (E⁄ℚ).Nonsingular x₀ y₀ := by
      have h2 := h
      rw [← hx₀, ← hy₀] at h2
      exact (Affine.baseChange_nonsingular (W := E)
        (f := Algebra.ofId ℚ (AlgebraicClosure ℚ))
        (algebraMap ℚ (AlgebraicClosure ℚ)).injective x₀ y₀).mp h2
    refine ⟨Affine.Point.some x₀ y₀ h₀, ?_⟩
    have hmap := Affine.Point.map_some
      (f := Algebra.ofId ℚ (AlgebraicClosure ℚ)) h₀
    rw [show Affine.Point.baseChange ℚ (AlgebraicClosure ℚ)
        (Affine.Point.some x₀ y₀ h₀) =
      Affine.Point.map (Algebra.ofId ℚ (AlgebraicClosure ℚ))
        (Affine.Point.some x₀ y₀ h₀) from rfl, hmap]
    subst hx₀ hy₀
    rfl

/-!
### Character bookkeeping on a stable line

The linear algebra of Serre's §4.1 analysis, PROVEN here: a stable line
`W` in a 2-dimensional mod-`ℓ` representation carries a unit-valued
sub-character `χ₁` (the scalar action on the rank-1 space `W`), the
quotient carries a quotient-character `χ₂`, and
`det ρ g = χ₁ g · χ₂ g` (the triangular determinant,
`LinearMap.det_eq_det_mul_det`).
-/

section CharacterBookkeeping

set_option backward.isDefEq.respectTransparency false in
/-- **Scalar character on a rank-`1` module** (PROVEN): a multiplicative
family of endomorphisms of a `1`-dimensional space over `F` is
given by a unit-valued character. -/
lemma exists_unit_character_of_finrank_one {F : Type*} [Field F]
    {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module F M]
    [Module.Finite F M] (hM : Module.finrank F M = 1)
    (Φ : G → Module.End F M)
    (hΦ1 : Φ 1 = 1) (hΦmul : ∀ g h : G, Φ (g * h) = Φ g * Φ h) :
    ∃ χ : G →* Fˣ, ∀ g v, Φ g v = (χ g : F) • v := by
  classical
  let b : Module.Basis (Fin 1) F M :=
    Module.finBasisOfFinrankEq F M hM
  have hm₀ne : (b 0 : M) ≠ 0 := b.ne_zero 0
  have hspan : ∀ v : M, ∃ c : F, v = c • b 0 := by
    intro v
    have h1 := b.sum_repr v
    rw [Fin.sum_univ_one] at h1
    exact ⟨b.repr v 0, h1.symm⟩
  have huniq : ∀ {a c : F}, a • (b 0 : M) = c • b 0 → a = c := by
    intro a c h
    have h2 : (a - c) • (b 0 : M) = 0 := by rw [sub_smul, h, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hm₀ne
  choose c hc using fun g => hspan (Φ g (b 0))
  have hone : c 1 = 1 := by
    apply huniq
    rw [← hc 1, hΦ1, Module.End.one_apply, one_smul]
  have hmul : ∀ g h, c (g * h) = c g * c h := by
    intro g h
    apply huniq
    rw [← hc (g * h), hΦmul, Module.End.mul_apply, hc h, map_smul, hc g,
      smul_smul, mul_comm (c h) (c g)]
  have hunit : ∀ g, c g * c g⁻¹ = 1 := fun g => by
    rw [← hmul, mul_inv_cancel, hone]
  refine ⟨MonoidHom.mk' (fun g =>
      ⟨c g, c g⁻¹, hunit g, (mul_comm (c g⁻¹) (c g)).trans (hunit g)⟩)
    (fun g h => Units.ext (hmul g h)), ?_⟩
  intro g v
  obtain ⟨a, rfl⟩ := hspan v
  show Φ g (a • b 0) = c g • a • b 0
  rw [map_smul, hc g, smul_smul, smul_smul, mul_comm]

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [DiscreteTopology F] {V : Type*} [AddCommGroup V]
  [Module F V] [Module.Finite F V]

omit [IsTopologicalRing F] [DiscreteTopology F] in
set_option backward.isDefEq.respectTransparency false in
/-- **The sub-character of a stable line** (PROVEN): the restriction of
the representation to a rank-`1` stable submodule is a unit-valued
character. -/
lemma exists_subCharacter (ρbar : GaloisRep ℚ F V)
    (W : Submodule F V) (hW1 : Module.finrank F W = 1)
    (hstable : ∀ g v, v ∈ W → ρbar g v ∈ W) :
    ∃ χ₁ : Field.absoluteGaloisGroup ℚ →* Fˣ,
      ∀ g, ∀ v ∈ W, ρbar g v = (χ₁ g : F) • v := by
  have he : ∀ g, W ≤ W.comap (ρbar g) := fun g v hv => hstable g v hv
  obtain ⟨χ₁, hχ₁⟩ := exists_unit_character_of_finrank_one hW1
    (fun g => (ρbar g).restrict (he g))
    (by
      apply LinearMap.ext; intro v; apply Subtype.ext
      rw [LinearMap.coe_restrict_apply, map_one, Module.End.one_apply,
        Module.End.one_apply])
    (by
      intro g h
      apply LinearMap.ext; intro v; apply Subtype.ext
      rw [LinearMap.coe_restrict_apply, map_mul, Module.End.mul_apply,
        Module.End.mul_apply, LinearMap.coe_restrict_apply,
        LinearMap.coe_restrict_apply])
  refine ⟨χ₁, fun g v hv => ?_⟩
  have h1 := hχ₁ g ⟨v, hv⟩
  have h2 := congrArg Subtype.val h1
  rw [LinearMap.coe_restrict_apply] at h2
  exact h2

omit [IsTopologicalRing F] [DiscreteTopology F] in
set_option backward.isDefEq.respectTransparency false in
/-- **The quotient-character of a stable line** (PROVEN): the induced
action on the quotient by a stable submodule with rank-`1` quotient is a
unit-valued character. -/
lemma exists_quotCharacter (ρbar : GaloisRep ℚ F V)
    (W : Submodule F V)
    (hQ1 : Module.finrank F (V ⧸ W) = 1)
    (hstable : ∀ g v, v ∈ W → ρbar g v ∈ W) :
    ∃ χ₂ : Field.absoluteGaloisGroup ℚ →* Fˣ,
      ∀ g v, W.mkQ (ρbar g v) = (χ₂ g : F) • W.mkQ v := by
  have he : ∀ g, W ≤ W.comap (ρbar g) := fun g v hv => hstable g v hv
  obtain ⟨χ₂, hχ₂⟩ := exists_unit_character_of_finrank_one hQ1
    (fun g => W.mapQ W (ρbar g) (he g))
    (by
      apply LinearMap.ext; intro z
      obtain ⟨v, rfl⟩ := W.mkQ_surjective z
      rw [Module.End.one_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
        map_one, Module.End.one_apply])
    (by
      intro g h
      apply LinearMap.ext; intro z
      obtain ⟨v, rfl⟩ := W.mkQ_surjective z
      rw [Module.End.mul_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
        Submodule.mapQ_apply, Submodule.mapQ_apply, map_mul,
        Module.End.mul_apply])
  refine ⟨χ₂, fun g v => ?_⟩
  have h1 := hχ₂ g (W.mkQ v)
  rw [Submodule.mkQ_apply, Submodule.mapQ_apply] at h1
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply]
  exact h1

omit [IsTopologicalRing F] [DiscreteTopology F] in
set_option backward.isDefEq.respectTransparency false in
/-- **The triangular determinant** (PROVEN): on a stable line, the
determinant is the product of the sub- and quotient-characters. -/
lemma det_eq_subCharacter_mul_quotCharacter
    (ρbar : GaloisRep ℚ F V)
    (W : Submodule F V) (hW1 : Module.finrank F W = 1)
    (hQ1 : Module.finrank F (V ⧸ W) = 1)
    (hstable : ∀ g v, v ∈ W → ρbar g v ∈ W)
    (χ₁ χ₂ : Field.absoluteGaloisGroup ℚ →* Fˣ)
    (hχ₁ : ∀ g, ∀ v ∈ W, ρbar g v = (χ₁ g : F) • v)
    (hχ₂ : ∀ g v, W.mkQ (ρbar g v) = (χ₂ g : F) • W.mkQ v)
    (g : Field.absoluteGaloisGroup ℚ) :
    LinearMap.det (ρbar g : Module.End F V) =
      (χ₁ g : F) * (χ₂ g : F) := by
  have he : W ≤ W.comap (ρbar g) := fun v hv => hstable g v hv
  rw [LinearMap.det_eq_det_mul_det W (ρbar g) he]
  congr 1
  · have hr : (ρbar g).restrict he =
        (χ₁ g : F) • (LinearMap.id : W →ₗ[F] W) := by
      apply LinearMap.ext; intro v; apply Subtype.ext
      rw [LinearMap.coe_restrict_apply, hχ₁ g v.1 v.2]
      rfl
    rw [hr, LinearMap.det_smul, hW1, pow_one, LinearMap.det_id, mul_one]
  · have hr : W.mapQ W (ρbar g) he =
        (χ₂ g : F) • (LinearMap.id : (V ⧸ W) →ₗ[F] (V ⧸ W)) := by
      apply LinearMap.ext; intro z
      obtain ⟨v, rfl⟩ := W.mkQ_surjective z
      have h2 : (W.mapQ W (ρbar g) he) (W.mkQ v) = W.mkQ (ρbar g v) := by
        rw [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.mkQ_apply]
      rw [h2, hχ₂ g v]
      rfl
    rw [hr, LinearMap.det_smul, hQ1, pow_one, LinearMap.det_id, mul_one]

set_option backward.isDefEq.respectTransparency false in
/-- **Openness of the kernel-level set of a mod-`ℓ`-style representation over a discrete field**
(PROVEN): the set where the representation is trivial is open — the
endomorphism space is discrete (finite module over the discrete
`F`), so the representation is locally constant. Stated with the
finiteness input as a plain hypothesis so that callers can supply it
for any definitionally-equal spelling of `V`. -/
lemma isOpen_setOf_galoisRep_eq_one {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [DiscreteTopology F]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρbar : GaloisRep ℚ F V) (hfinV : Finite V) :
    IsOpen {g : Field.absoluteGaloisGroup ℚ | ρbar g = 1} := by
  haveI := hfinV
  letI := moduleTopology F (Module.End F V)
  haveI : Finite (Module.End F V) :=
    Finite.of_injective (fun f => (f : V → V)) DFunLike.coe_injective
  haveI : Module.Finite F (Module.End F V) :=
    Module.Finite.of_finite
  haveI : DiscreteTopology (Module.End F V) :=
    GaloisRepresentation.discreteTopology_moduleTopology F
      (Module.End F V)
  have hcont : Continuous fun g : Field.absoluteGaloisGroup ℚ => ρbar g :=
    ρbar.continuous_toFun
  exact (isOpen_discrete ({1} : Set (Module.End F V))).preimage hcont

set_option backward.isDefEq.respectTransparency false in
/-- **Unipotent scalars are trivial** (PROVEN): if `(f − 1)² = 0` and
`f` acts on a nonzero vector by the scalar `c`, then `c = 1` — the
eigenvalues of a unipotent endomorphism are `1`. -/
lemma subCharacter_eq_one_of_sq_eq_zero {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [DiscreteTopology F]
    {V : Type*} [AddCommGroup V] [Module F V]
    (f : Module.End F V) (hf : (f - 1) ^ 2 = 0)
    {c : F} {w : V} (hw : w ≠ 0) (hcw : f w = c • w) : c = 1 := by
  have h1 : (f - 1) w = (c - 1) • w := by
    rw [LinearMap.sub_apply, Module.End.one_apply, hcw, sub_smul, one_smul]
  have h2 : ((f - 1) ^ 2 : Module.End F V) w =
      ((c - 1) ^ 2 : F) • w := by
    rw [pow_two, Module.End.mul_apply, h1, map_smul, h1, smul_smul,
      ← pow_two]
  rw [hf] at h2
  have h3 : ((c - 1) ^ 2 : F) • w = 0 := by
    rw [← h2]
    rfl
  rcases smul_eq_zero.mp h3 with h4 | h4
  · have h5 : (c - 1 : F) = 0 := pow_eq_zero_iff two_ne_zero |>.mp h4
    have h6 := sub_eq_zero.mp h5
    exact h6
  · exact absurd h4 hw

set_option backward.isDefEq.respectTransparency false in
/-- **Unipotent quotient scalars are trivial** (PROVEN): if
`(f − 1)² = 0` and `f` descends to the scalar `c` on the (nontrivial)
quotient by a stable submodule, then `c = 1`. -/
lemma quotCharacter_eq_one_of_sq_eq_zero {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [DiscreteTopology F]
    {V : Type*} [AddCommGroup V] [Module F V]
    (f : Module.End F V) (hf : (f - 1) ^ 2 = 0)
    (W : Submodule F V) (hWtop : W ≠ ⊤) {c : F}
    (hc : ∀ v, W.mkQ (f v) = c • W.mkQ v) : c = 1 := by
  haveI : Nontrivial (V ⧸ W) := Submodule.Quotient.nontrivial_iff.mpr hWtop
  obtain ⟨z, hz⟩ := exists_ne (0 : V ⧸ W)
  obtain ⟨v, rfl⟩ := W.mkQ_surjective z
  have h1 : ∀ u, W.mkQ ((f - 1) u) = (c - 1 : F) • W.mkQ u := by
    intro u
    rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, hc, sub_smul,
      one_smul]
  have h2 : W.mkQ (((f - 1) ^ 2 : Module.End F V) v) =
      ((c - 1) ^ 2 : F) • W.mkQ v := by
    rw [pow_two, Module.End.mul_apply, h1 ((f - 1) v), h1 v, smul_smul,
      ← pow_two]
  rw [hf] at h2
  have h3 : ((c - 1) ^ 2 : F) • W.mkQ v = 0 := by
    rw [← h2]
    show W.mkQ ((0 : Module.End F V) v) = 0
    rw [LinearMap.zero_apply, map_zero]
  rcases smul_eq_zero.mp h3 with h4 | h4
  · exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h4)
  · exact absurd h4 hz

end CharacterBookkeeping

section GenericBridge

variable {K : Type*} [Field K] [NumberField K]

set_option backward.isDefEq.respectTransparency false in
/-- **Characters through an unramified representation are unramified**
(PROVEN, stated over a GENERIC number field so that the `algebraMap`
spelling agrees definitionally with the one inside `GaloisRep.toLocal`
— at `K = ℚ` a locally-elaborated `algebraMap` picks `Rat`-specific
instance paths that instance- and even default-transparency
unification cannot reconcile with the generic ones, because
`Field.absoluteGaloisGroup.map` is not exposed; callers at `ℚ` bridge
the two spellings with `Rat.subsingleton_ringHom` + `convert`): if the
representation kills the local inertia at `v` and `χ` is trivial
wherever the representation is, then the restriction of `χ` to the
local Galois group kills inertia. -/
lemma character_localInertia_le_ker_of_isUnramifiedAt {F : Type*}
    [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρbar : GaloisRep K F V)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hUn : ρbar.IsUnramifiedAt v)
    (χ : Field.absoluteGaloisGroup K →* Fˣ)
    (htriv : ∀ g, ρbar g = 1 → χ g = 1) :
    localInertiaGroup v ≤ (χ.comp (Field.absoluteGaloisGroup.map
      (algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion
        K v))).toMonoidHom).ker := by
  intro σ hσ
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
  apply htriv
  have h1 : (ρbar.toLocal v) σ = 1 := hUn.localInertiaGroup_le hσ
  exact h1

end GenericBridge

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Unipotence of inertia at `2`** (DERIVED 2026-07-17 from the
pointwise Tate unipotence leaf and the PROVEN transport machinery): the
Frey curve has multiplicative reduction at `2`
(`freyCurve_hasMultiplicativeReduction_at_two`, PROVEN), so every
element of the local inertia group at `2` acts on the `p`-torsion with
`(ρ(σ) − 1)² = 0` — the pointwise statement
`torsion_unipotent_of_multiplicative_reduction` at the embedded
valuation subring, carried over by
`map_mem_inertiaSubgroup_of_mem_localInertiaGroup` and expanded
`(A − 1)² = A·A − A − A + 1` pointwise on the torsion. -/
theorem FreyPackage.inertia_two_unipotent (P : FreyPackage) :
    haveI : Fact P.p.Prime := ⟨P.pp⟩
    ∀ σ ∈ localInertiaGroup
      Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat,
      (P.freyCurve.galoisRep P.p P.hppos
          ((Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat))) σ) -
        1) ^ 2 = 0 := by
  haveI : Fact P.p.Prime := ⟨P.pp⟩
  intro σ hσ
  haveI := P.freyCurve_hasMultiplicativeReduction_at_two
  have hp2 : (2 : ℕ) ≠ P.p := by
    have := P.hp5
    omega
  have hpt := WeierstrassCurve.torsion_unipotent_of_multiplicative_reduction
    P.freyCurve Nat.prime_two hp2 σ hσ
  set A := P.freyCurve.galoisRep P.p P.hppos
    ((Field.absoluteGaloisGroup.map (algebraMap ℚ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat))) σ)
  apply LinearMap.ext
  intro v
  have hexp : ((A - 1) ^ 2 : Module.End (ZMod P.p)
      ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p)) v =
      A (A v) - A v - A v + v := by
    rw [pow_two, Module.End.mul_apply, LinearMap.sub_apply,
      Module.End.one_apply, LinearMap.sub_apply, Module.End.one_apply,
      map_sub]
    abel
  rw [hexp]
  have hv : ((v : ((P.freyCurve.map (algebraMap ℚ
      (AlgebraicClosure ℚ))).nTorsion P.p)) :
      ((P.freyCurve.map (algebraMap ℚ
        (AlgebraicClosure ℚ)))⁄(AlgebraicClosure ℚ)).Point) ∈
      AddSubgroup.torsionBy
        ((P.freyCurve.map (algebraMap ℚ
          (AlgebraicClosure ℚ)))⁄(AlgebraicClosure ℚ)).Point
        ((P.p : ℕ) : ℤ) := by
    have h1 := v.2
    rw [Submodule.mem_torsionBy_iff] at h1
    show ((P.p : ℕ) : ℤ) • (v : ((P.freyCurve.map (algebraMap ℚ
      (AlgebraicClosure ℚ)))⁄(AlgebraicClosure ℚ)).Point) = 0
    exact_mod_cast h1
  have hp := hpt v.1 hv
  apply Subtype.ext
  have hb : ∀ w : ((P.freyCurve.map (algebraMap ℚ
      (AlgebraicClosure ℚ))).nTorsion P.p),
      (show ((P.freyCurve)⁄(AlgebraicClosure ℚ)).Point from (A w).1) =
      WeierstrassCurve.Affine.Point.map
        (((Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat))) σ :
          AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom
        (show ((P.freyCurve)⁄(AlgebraicClosure ℚ)).Point from w.1) :=
    fun w => rfl
  have hgoal : (show ((P.freyCurve)⁄(AlgebraicClosure ℚ)).Point from
      (A (A v) - A v - A v + v : ((P.freyCurve.map (algebraMap ℚ
        (AlgebraicClosure ℚ))).nTorsion P.p)).1) =
      (show ((P.freyCurve)⁄(AlgebraicClosure ℚ)).Point from (A (A v)).1) -
      (show ((P.freyCurve)⁄(AlgebraicClosure ℚ)).Point from (A v).1) -
      (show ((P.freyCurve)⁄(AlgebraicClosure ℚ)).Point from (A v).1) +
      (show ((P.freyCurve)⁄(AlgebraicClosure ℚ)).Point from v.1) := rfl
  show (show ((P.freyCurve)⁄(AlgebraicClosure ℚ)).Point from
    (A (A v) - A v - A v + v : ((P.freyCurve.map (algebraMap ℚ
      (AlgebraicClosure ℚ))).nTorsion P.p)).1) =
    (show ((P.freyCurve)⁄(AlgebraicClosure ℚ)).Point from
      ((0 : Module.End (ZMod P.p) ((P.freyCurve.map (algebraMap ℚ
        (AlgebraicClosure ℚ))).nTorsion P.p)) v).1)
  rw [hgoal, hb (A v), hb v]
  exact hp

/-!
### Decomposition of the flat/ordinary analysis at `p` (2026-07-22)

`subquotient_character_unramified_at_p` is decomposed into two
reduction-type leaves producing an *étale line* `L` — a line in the
`p`-torsion on whose QUOTIENT the inertia at `p` acts trivially — and a
PROVEN linear-algebra assembly. After the third pass (2026-07-22,
night) the two reduction-type nodes are themselves DERIVED from three
sharper leaves cut along the same seams as the `Semistable.lean`
development:

After the fourth pass (2026-07-23) BOTH multiplicative leaves are
PROVEN, assembled from three new pieces cut at the `Semistable.lean`
seams:

* `exists_localTorsionQuotient_of_split` (PROVEN): the local Kummer
  content — the `p`-torsion of a split-multiplicative curve over
  `ℚ_qˆ` surjects onto `ℤ/p` by the Tate-parameter exponent
  (`exists_tateTorsionQuotient`), invariantly under the WHOLE local
  Galois group; no residue-characteristic hypothesis, so valid at
  `q = p`. The kernel is the `μ_p`-line.
* `exists_localTorsionQuotient_of_nonsplit` (PROVEN): the same
  quotient for a nonsplit-multiplicative curve, invariant under local
  INERTIA, by transport along the unramified quadratic twist.
* `exists_etale_line_of_localTorsionQuotient` (PROVEN): the
  `ℚ̄`-pullback glue — the chosen embedding is a bijection on
  `p`-torsion (`p²`-count on both sides), the pulled-back functional
  is `ℤ/p`-linear and surjective, its kernel is the étale line by
  rank-nullity.
* `exists_etale_line_of_split_multiplicative_self` (DERIVED
  2026-07-23 from the first and third pieces). Silverman ATAEC V.3,
  V.5.
* `exists_etale_line_of_nonsplit_multiplicative_self` (DERIVED
  2026-07-23 from the second and third pieces). Silverman ATAEC
  V.5.4.
* `exists_etale_line_of_multiplicative_self` (DERIVED 2026-07-22 from
  the two preceding nodes by the split/nonsplit case split, via
  `hasMultiplicativeReduction_adicCompletion`).
* `exists_etale_line_of_good_of_inertia_stable_line` (DERIVED
  2026-07-23 from the two leaves below by the tautological fork on
  the vanishing of the reduced curve's geometric `p`-torsion): at a
  prime `p ≠ 2` of good reduction, an INERTIA-stable line of `E[p]`
  forces ordinary reduction, and the connected-étale sequence of
  `E[p]/ℤ_p` then provides the étale-quotient line. Serre Duke 1987,
  §4.1.
* `exists_etale_line_of_good_of_ordinary` (DERIVED 2026-07-23 from
  the local leaf below through the PROVEN reduction-agnostic pullback
  glue `exists_etale_line_of_localTorsionQuotient`): at a good
  ordinary prime `p ≠ 2` (the reduced curve has a nonzero geometric
  `p`-torsion point), the connected line of the connected-étale
  sequence of `E[p]/ℤ_p` has inertia-trivial quotient.
* `exists_localTorsionQuotient_of_good_ordinary` (DERIVED 2026-07-25
  from the two bricks below): the local `p`-torsion surjects onto
  `ℤ/p` inertia-invariantly; the kernel is the formal-group line. The
  quotient is `red` corestricted to `Ẽ(𝔽̄_p)[p]`, which is cyclic of
  order `p`, hence `≅ ℤ/p` (`zmodAddEquivOfGenerator`).
  * `exists_localReductionHom_of_good_reduction` (DERIVED 2026-07-25
    from the two bricks below by lift-and-correct — the GEOMETRY): an
    inertia-invariant reduction homomorphism from the local
    `p`-torsion onto the `p`-torsion of the reduced curve.
    * `exists_localReductionAddHom_of_good_reduction` (sorry node —
      the reduction map itself, on ALL local points: a group
      homomorphism, surjective onto `Ẽ(𝔽̄_p)` by Hensel, invariant
      under inertia because inertia acts trivially on the residue
      field, with kernel exactly the non-integral locus
      `x ∉ localValuationSubring`). Silverman *AEC* VII.2.
    * `exists_localKernelDivision_of_good_reduction` (PROVEN
      2026-07-25 — that kernel is `p`-divisible over `ℚ̄_p`; false
      over any finite extension of `ℚ_p`). Proven not by the Newton
      polygon of `[p]` but by a DIVISION-POLYNOMIAL argument:
      `Φ_p − x · Ψ²_p` is monic, and good reduction makes a
      coefficient of `Ψ²_p` a unit, which forces one of its roots to
      be non-integral.
  * `card_torsion_reduction_of_good_ordinary` (DERIVED 2026-07-25 —
    the CHARACTERISTIC-`p` content): ordinarity makes `Ẽ(𝔽̄_p)[p]` of
    order exactly `p`. Its residual gap is now the single
    local-field-free leaf
    * `card_torsionBy_dvd_of_charP` (no direct sorry): over an
      algebraically closed field in which `p` vanishes, the geometric
      `p`-torsion of an elliptic curve has order dividing `p` —
      inseparability of the multiplication-by-`p` isogeny. The
      residue-characteristic half is PROVEN
      (`residue_natCast_eq_zero_of_prime`), and ordinarity excluding
      the trivial case is proven glue.
* `not_inertia_stable_line_of_good_of_supersingular` (DERIVED
  2026-07-23 from the local eigenvector leaf below by transporting a
  generator of the stable line along the chosen embedding
  `ℚ̄ ↪ ℚ̂̄_p`): at a good supersingular prime `p ≠ 2` (the reduced
  curve has trivial geometric `p`-torsion), no line of `E[p]` is
  inertia-stable.
* `not_local_inertia_eigenvector_of_good_of_supersingular` (skeleton
  written 2026-07-25 over two bricks; the linear-algebra brick PROVEN
  2026-07-25, so the ONLY remaining gap is the arithmetic one): no
  nonzero local `p`-torsion point is an inertia eigenvector — inertia
  acts through the level-2 fundamental character, whose eigenvalues are
  `𝔽_{p²}`-conjugate and not `𝔽_p`-rational (Serre, Propriétés
  galoisiennes…, Invent. Math. 15 (1972), §1.11–1.12, Prop. 12). The
  two bricks are
  * `exists_local_inertia_torsion_order_of_good_of_supersingular`
    (the ARITHMETIC: an inertia element no power of which acts
    trivially unless `p + 1` divides the exponent, i.e. the
    order-`(p² − 1)` nonsplit-Cartan generator) — DERIVED 2026-07-25
    from the one-point cut
    * `exists_local_inertia_torsion_orbit_of_good_of_supersingular`
      (DERIVED 2026-07-25 over the two bricks
      `spectralNorm_torsion_abscissa_of_good_of_supersingular` (the
      Newton polygon of the `p`-division polynomial) and
      `exists_localInertia_tameCharacter_orbit` (surjectivity of the tame
      character of local inertia)): the same inertia element with a SINGLE `p`-torsion
      point `Q` whose `⟨σ⟩`-orbit has length divisible by `p + 1`. The
      nonsplit Cartan acts simply transitively on the `p² − 1` nonzero
      points of `E[p]`, so the orbit is everything; the module-wide
      statement follows by instantiating at `Q`. Its docstring carries
      the four-step route (reduction kernel → Newton-polygon slope of
      the `p`-division polynomial → tame ramification → the PROVEN
      compactness lifting into `localInertiaGroup`), and
  * the `hborel` step inside the proof (the LINEAR ALGEBRA: an
    eigenvector makes the whole inertia image upper-triangular, hence
    of exponent dividing `p (p − 1)`) — PROVEN 2026-07-25 from the
    abstract Borel bound `borel_bound_iterate_eq_self` through the
    curve-level `point_map_pow_eq_self_of_eigenvector`. The two bricks
    are contradictory because `p + 1 ∤ p (p − 1)` — proven arithmetic
    in the same proof.
* `exists_etale_line_or_no_stable_line_of_good` (DERIVED 2026-07-23
  from the preceding leaf by the tautological fork on the existence
  of an inertia-stable line).
* `exists_etale_line_of_good_of_stable_line` (DERIVED 2026-07-22 from
  the dichotomy node: the given stable line refutes the second
  disjunct).
* `character_unramified_at_p_of_etale_line` (PROVEN): given ANY such
  line `L`, either the stable line `W` equals `L` — then `χ₂` is the
  quotient character of `L` and is unramified at `p` — or `W ∩ L = 0` —
  then `W` maps isomorphically onto the quotient by `L`, forcing
  `χ₁` to be trivial on inertia at `p`.
-/

open ValuativeRel IsDedekindDomain in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **The local Tate torsion quotient, split multiplicative case**
(PROVEN 2026-07-23 — the pure Kummer statement, valid at `q = p`
because no residue-characteristic hypothesis is needed): for a curve
`X/ℚ_qˆ` with split multiplicative reduction and any `p ≠ 0`, the
`p`-torsion of `X` over the local algebraic closure carries a
surjective additive map onto `ℤ/p` — the Tate-parameter exponent of
`exists_tateTorsionQuotient`, the quotient of the filtration
`0 → μ_p → X[p] → ℤ/p → 0` — invariant under the WHOLE local Galois
group. Its kernel is the `μ_p`-line, the étale line of the split
multiplicative case. Silverman ATAEC V.3, V.5. -/
theorem WeierstrassCurve.exists_localTorsionQuotient_of_split {q : ℕ}
    (hq : q.Prime)
    (X : WeierstrassCurve (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) [X.IsElliptic]
    [X.HasSplitMultiplicativeReduction
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat]]
    {p : ℕ} (hp : p ≠ 0) :
    ∃ π : AddSubgroup.torsionBy
        ((X⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))).Point ((p : ℕ) : ℤ) →+
        ZMod p,
      Function.Surjective π ∧
      ∀ (σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))
          ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat]
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)))
        (P Q : AddSubgroup.torsionBy
          ((X⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)))).Point ((p : ℕ) : ℤ)),
        (Q : ((X⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))).Point) =
          WeierstrassCurve.Affine.Point.map (W' := X) σ.toAlgHom
            (P : ((X⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat)))).Point) →
        π Q = π P := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharZero (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) :=
    ((algebraMap (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))).charZero_iff
      (algebraMap (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))).injective).mp inferInstance
  obtain ⟨e, he⟩ := WeierstrassCurve.exists_tateEquivSepClosure
    (k := HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)
    (E := X)
    (Ω := AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))
  obtain ⟨π, hπsurj, hπinv⟩ := WeierstrassCurve.exists_tateTorsionQuotient
    (k := HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)
    (E := X)
    (Ω := AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))
    e he hp (Nat.cast_ne_zero.mpr hp)
  exact ⟨π, hπsurj, fun σ P Q hQ => hπinv σ P Q hQ⟩

open ValuativeRel IsDedekindDomain in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 4000000 in
/-- **The local Tate torsion quotient, nonsplit multiplicative case**
(PROVEN 2026-07-23 — the unramified quadratic-twist descent of the
split-case quotient): for a curve `X/ℚ_qˆ` with multiplicative but not
split reduction, the `p`-torsion over the local algebraic closure
still surjects onto `ℤ/p`, invariantly under the local INERTIA. The
unramified quadratic twist
(`exists_quadraticTwist_hasSplitMultiplicativeReduction`) has split
multiplicative reduction; its Galois-equivariant point equivalence
`quadraticTwistPointEquiv` commutes with every inertia element (the
quadratic character is trivial there:
`inertia_fixes_algHom_of_unramified_gen`), so the split-case quotient
transports. Silverman ATAEC V.5.4; Serre Duke 1987, §4.1. -/
theorem WeierstrassCurve.exists_localTorsionQuotient_of_nonsplit {q : ℕ}
    (hq : q.Prime)
    (X : WeierstrassCurve (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) [X.IsElliptic]
    [X.HasMultiplicativeReduction 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat]]
    (hnonsplit : ¬ X.HasSplitMultiplicativeReduction
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat])
    {p : ℕ} (hp : p ≠ 0) :
    ∃ π : AddSubgroup.torsionBy
        ((X⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))).Point ((p : ℕ) : ℤ) →+
        ZMod p,
      Function.Surjective π ∧
      ∀ σ ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat,
        ∀ (P Q : AddSubgroup.torsionBy
          ((X⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)))).Point ((p : ℕ) : ℤ)),
        (Q : ((X⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))).Point) =
          WeierstrassCurve.Affine.Point.map (W' := X)
            ((σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))
              ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat]
              (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))).toAlgHom
            (P : ((X⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat)))).Point) →
        π Q = π P := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨L, _, _, _, _, hsplit', θL, Qgen, hQm, hθtop, hθQ, hQsep⟩ :=
    WeierstrassCurve.exists_quadraticTwist_hasSplitMultiplicativeReduction
      (E := X) (R := 𝒪[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat]) hnonsplit
  set Tw : WeierstrassCurve (HeightOneSpectrum.adicCompletion ℚ
    hq.toHeightOneSpectrumRingOfIntegersRat) := X.quadraticTwist L
  set Mt : WeierstrassCurve (HeightOneSpectrum.adicCompletion ℚ
    hq.toHeightOneSpectrumRingOfIntegersRat) := Tw.minimal
    𝒪[HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat]
  set Cb : WeierstrassCurve.VariableChange (AlgebraicClosure
    (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) :=
    ((Tw.exists_isMinimal 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat]).choose.baseChange
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) with hCbdef
  haveI hMtsplit : Mt.HasSplitMultiplicativeReduction
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat] := hsplit'
  haveI hTwell : Tw.IsElliptic :=
    inferInstanceAs ((X.quadraticTwist L).IsElliptic)
  haveI hMtell : Mt.IsElliptic :=
    inferInstanceAs (((Tw.exists_isMinimal
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat]).choose • Tw).IsElliptic)
  haveI hTwΩell : (Tw⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))).IsElliptic :=
    inferInstanceAs ((Tw.map (algebraMap (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))).IsElliptic)
  letI algLΩ : Algebra L (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) :=
    (IsAlgClosed.lift (M := AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))
      (R := HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) (S := L)).toAlgebra
  haveI : IsScalarTower (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) L
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      ((IsAlgClosed.lift (M := AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))
        (R := HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)
        (S := L)).commutes x).symm)
  have hEq : (Mt⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))) =
      Cb • (Tw⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) :=
    (WeierstrassCurve.baseChange_smul_baseChange _ _ _).symm
  let Φ : ((Mt⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))).Point) ≃+
      ((X⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))).Point) :=
    ((WeierstrassCurve.Affine.Point.equivOfEq hEq).trans
      (WeierstrassCurve.Affine.Point.equivVariableChange
        (Tw⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))) Cb)).trans
      (X.quadraticTwistPointEquiv L (AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))
  -- torsion transports backwards along `Φ`
  have hΦsymmtor : ∀ Q : AddSubgroup.torsionBy
      ((X⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))).Point ((p : ℕ) : ℤ),
      Φ.symm (Q : ((X⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))).Point) ∈
      AddSubgroup.torsionBy
        ((Mt⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))).Point ((p : ℕ) : ℤ) := by
    intro Q
    show ((p : ℕ) : ℤ) • Φ.symm (Q : ((X⁄(AlgebraicClosure
      (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))).Point) = 0
    rw [← map_zsmul Φ.symm,
      (show ((p : ℕ) : ℤ) • (Q : ((X⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))).Point) = 0 from Q.2),
      map_zero]
  -- the split-case quotient of the minimal twist
  obtain ⟨π₀, hπ₀surj, hπ₀inv⟩ :=
    WeierstrassCurve.exists_localTorsionQuotient_of_split hq Mt hp
  -- the transported quotient
  let π : AddSubgroup.torsionBy
      ((X⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))).Point ((p : ℕ) : ℤ) →+
      ZMod p :=
    AddMonoidHom.mk' (fun Q => π₀ ⟨Φ.symm (Q : ((X⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))).Point), hΦsymmtor Q⟩)
      (fun Q₁ Q₂ => by
        have h1 : (⟨Φ.symm ((Q₁ + Q₂ : AddSubgroup.torsionBy
            ((X⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat)))).Point
            ((p : ℕ) : ℤ)) : ((X⁄(AlgebraicClosure
            (HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat)))).Point),
            hΦsymmtor (Q₁ + Q₂)⟩ : AddSubgroup.torsionBy
            ((Mt⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat)))).Point
            ((p : ℕ) : ℤ)) =
            ⟨Φ.symm (Q₁ : ((X⁄(AlgebraicClosure
              (HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))).Point),
              hΦsymmtor Q₁⟩ +
            ⟨Φ.symm (Q₂ : ((X⁄(AlgebraicClosure
              (HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))).Point),
              hΦsymmtor Q₂⟩ := by
          apply Subtype.ext
          show Φ.symm ((Q₁ : ((X⁄(AlgebraicClosure
              (HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))).Point) +
              (Q₂ : ((X⁄(AlgebraicClosure
              (HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))).Point)) = _
          rw [map_add Φ.symm]
          rfl
        rw [h1, map_add])
  refine ⟨π, ?_, ?_⟩
  · -- surjectivity: `Φ` transports the split-case surjectivity
    intro c
    obtain ⟨R₀, hR₀⟩ := hπ₀surj c
    have hΦtor : Φ (R₀ : ((Mt⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))).Point) ∈
        AddSubgroup.torsionBy
        ((X⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))).Point ((p : ℕ) : ℤ) := by
      show ((p : ℕ) : ℤ) • Φ (R₀ : ((Mt⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))).Point) = 0
      rw [← map_zsmul Φ,
        (show ((p : ℕ) : ℤ) • (R₀ : ((Mt⁄(AlgebraicClosure
          (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)))).Point) = 0 from R₀.2),
        map_zero]
    refine ⟨⟨Φ (R₀ : ((Mt⁄(AlgebraicClosure
      (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))).Point), hΦtor⟩, ?_⟩
    have h2 : (⟨Φ.symm (Φ (R₀ : ((Mt⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))).Point)),
        hΦsymmtor ⟨Φ (R₀ : ((Mt⁄(AlgebraicClosure
          (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)))).Point), hΦtor⟩⟩ :
        AddSubgroup.torsionBy
        ((Mt⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))).Point ((p : ℕ) : ℤ)) =
        R₀ := Subtype.ext (Φ.symm_apply_apply _)
    calc π ⟨Φ (R₀ : ((Mt⁄(AlgebraicClosure
          (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)))).Point), hΦtor⟩
        = π₀ ⟨Φ.symm (Φ (R₀ : ((Mt⁄(AlgebraicClosure
            (HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat)))).Point)),
            hΦsymmtor ⟨Φ (R₀ : ((Mt⁄(AlgebraicClosure
              (HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))).Point),
              hΦtor⟩⟩ := rfl
      _ = π₀ R₀ := by rw [h2]
      _ = c := hR₀
  · -- invariance under inertia: the twist equivalence commutes
    intro σ hσ P Q hQ
    set σΩ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))
        ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat]
        (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)) :=
      (σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))
        ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat]
        (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))
    have hfixL : ∀ y : L,
        σΩ (algebraMap L (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)) y) =
        algebraMap L (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)) y :=
      fun y => inertia_fixes_algHom_of_unramified_gen hq θL hθtop Qgen hQm
        hθQ hQsep
        ⟨σΩ, mem_decompositionSubgroup_localValuationSubring _ σΩ⟩
        (mem_inertiaSubgroup_localValuationSubring _ σΩ hσ)
        (IsAlgClosed.lift) y
    have hσu : σΩ.toAlgHom ((Cb.u : AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))) =
        (Cb.u : AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)) := by
      rw [hCbdef]
      simp only [WeierstrassCurve.VariableChange.baseChange,
        WeierstrassCurve.VariableChange.map, Units.coe_map, MonoidHom.coe_coe]
      exact σΩ.toAlgHom.commutes _
    have hσr : σΩ.toAlgHom Cb.r = Cb.r := by
      rw [hCbdef]
      simp only [WeierstrassCurve.VariableChange.baseChange,
        WeierstrassCurve.VariableChange.map]
      exact σΩ.toAlgHom.commutes _
    have hσs : σΩ.toAlgHom Cb.s = Cb.s := by
      rw [hCbdef]
      simp only [WeierstrassCurve.VariableChange.baseChange,
        WeierstrassCurve.VariableChange.map]
      exact σΩ.toAlgHom.commutes _
    have hσt : σΩ.toAlgHom Cb.t = Cb.t := by
      rw [hCbdef]
      simp only [WeierstrassCurve.VariableChange.baseChange,
        WeierstrassCurve.VariableChange.map]
      exact σΩ.toAlgHom.commutes _
    have hcomm : ∀ Qt : ((Mt⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).Point),
        Φ (WeierstrassCurve.Affine.Point.map (W' := Mt) σΩ.toAlgHom Qt) =
        WeierstrassCurve.Affine.Point.map (W' := X) σΩ.toAlgHom (Φ Qt) := by
      intro Qt
      have h12 : (WeierstrassCurve.Affine.Point.equivVariableChange
          (Tw⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))) Cb)
          ((WeierstrassCurve.Affine.Point.equivOfEq hEq)
            (WeierstrassCurve.Affine.Point.map (W' := Mt) σΩ.toAlgHom Qt)) =
          WeierstrassCurve.Affine.Point.map (W' := Tw) σΩ.toAlgHom
            ((WeierstrassCurve.Affine.Point.equivVariableChange
              (Tw⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))) Cb)
              ((WeierstrassCurve.Affine.Point.equivOfEq hEq) Qt)) := by
        cases Qt with
        | zero => simp [← WeierstrassCurve.Affine.Point.zero_def]
        | some x y hxy =>
          rw [WeierstrassCurve.Affine.Point.map_some,
            WeierstrassCurve.Affine.Point.equivOfEq_some,
            WeierstrassCurve.Affine.Point.equivOfEq_some,
            WeierstrassCurve.Affine.Point.equivVariableChange_some,
            WeierstrassCurve.Affine.Point.equivVariableChange_some,
            WeierstrassCurve.Affine.Point.map_some]
          refine WeierstrassCurve.Affine.Point.some_eq_some _ ?_ ?_
          · simp only [map_add, map_mul, map_pow, hσu, hσr]
          · simp only [map_add, map_mul, map_pow, hσu, hσs, hσt]
      show (X.quadraticTwistPointEquiv L (AlgebraicClosure
          (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)))
          ((WeierstrassCurve.Affine.Point.equivVariableChange
            (Tw⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))) Cb)
            ((WeierstrassCurve.Affine.Point.equivOfEq hEq)
              (WeierstrassCurve.Affine.Point.map (W' := Mt)
                σΩ.toAlgHom Qt))) = _
      rw [h12]
      have hχ : quadraticCharacter (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat) L
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) σΩ = 1 :=
        (quadraticCharacter_eq_one_iff _ _ _ _).mpr hfixL
      have h3 := X.quadraticTwistPointEquiv_galois L
        (M := AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)) σΩ
        ((WeierstrassCurve.Affine.Point.equivVariableChange
          (Tw⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))) Cb)
          ((WeierstrassCurve.Affine.Point.equivOfEq hEq) Qt))
      rw [hχ, Units.val_one, one_zsmul] at h3
      exact h3
    -- transport the defining equation of `Q` through `Φ.symm`
    have h1 : Φ.symm (Q : ((X⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))).Point) =
        WeierstrassCurve.Affine.Point.map (W' := Mt) σΩ.toAlgHom
          (Φ.symm (P : ((X⁄(AlgebraicClosure
            (HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat)))).Point)) := by
      apply Φ.injective
      rw [Φ.apply_symm_apply, hcomm, Φ.apply_symm_apply]
      exact hQ
    have h2 : WeierstrassCurve.Affine.Point.map (W' := Mt) σΩ.toAlgHom
        (Φ.symm (P : ((X⁄(AlgebraicClosure
          (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)))).Point)) ∈
        AddSubgroup.torsionBy
        ((Mt⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))).Point ((p : ℕ) : ℤ) := by
      rw [← h1]
      exact hΦsymmtor Q
    calc π Q = π₀ ⟨Φ.symm (Q : ((X⁄(AlgebraicClosure
          (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)))).Point),
          hΦsymmtor Q⟩ := rfl
      _ = π₀ ⟨WeierstrassCurve.Affine.Point.map (W' := Mt) σΩ.toAlgHom
            (Φ.symm (P : ((X⁄(AlgebraicClosure
              (HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))).Point)), h2⟩ :=
          congrArg π₀ (Subtype.ext h1)
      _ = π₀ ⟨Φ.symm (P : ((X⁄(AlgebraicClosure
            (HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat)))).Point),
            hΦsymmtor P⟩ :=
          hπ₀inv σΩ
            ⟨Φ.symm (P : ((X⁄(AlgebraicClosure
              (HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))).Point),
              hΦsymmtor P⟩
            ⟨WeierstrassCurve.Affine.Point.map (W' := Mt) σΩ.toAlgHom
              (Φ.symm (P : ((X⁄(AlgebraicClosure
                (HeightOneSpectrum.adicCompletion ℚ
                  hq.toHeightOneSpectrumRingOfIntegersRat)))).Point)), h2⟩
            rfl
      _ = π P := rfl

open ValuativeRel IsDedekindDomain in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 4000000 in
/-- **From a local torsion quotient to a global étale line** (PROVEN
2026-07-23 — the `ℚ̄`-pullback glue common to the two multiplicative
étale-line leaves): given a surjective inertia-invariant additive map
`π` from the local `p`-torsion onto `ℤ/p`, the chosen embedding
`ℚ̄ ↪ ℚ_pᵃˡᵍ` (a BIJECTION on `p`-torsion: injectivity of `Point.map`
plus the `p²`-count on both sides) pulls `π` back to a surjective
`ℤ/p`-linear functional on `E[p](ℚ̄)`; its kernel is a line by
rank-nullity, and inertia acts trivially on the quotient by the
invariance of `π` transported through the equivariance
`point_map_algClosureEmbeddingRat_comm`. -/
theorem WeierstrassCurve.exists_etale_line_of_localTorsionQuotient
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : p.Prime)
    (π : AddSubgroup.torsionBy
        ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
          (HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat))).Point ((p : ℕ) : ℤ) →+
        ZMod p)
    (hπsurj : Function.Surjective π)
    (hπinv : ∀ σ ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat,
      ∀ (P Q : AddSubgroup.torsionBy
        ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
          (HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat))).Point ((p : ℕ) : ℤ)),
        (Q : ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
          (HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat))).Point) =
          WeierstrassCurve.Affine.Point.map
            (W' := E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
              hp.toHeightOneSpectrumRingOfIntegersRat)))
            ((σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat))
              ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat]
              (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat)))).toAlgHom
            (P : ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
              hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat))).Point) →
        π Q = π P) :
    ∃ L : Submodule (ZMod p)
        ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p),
      Module.finrank (ZMod p) L = 1 ∧
      ∀ σ ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat,
        ∀ v, L.mkQ (E.galoisRep p hp.pos
            ((Field.absoluteGaloisGroup.map (algebraMap ℚ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat))) σ) v) = L.mkQ v := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  letI := algebraRatAlgClosureAdic hp.toHeightOneSpectrumRingOfIntegersRat
  haveI : CharZero (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hp.toHeightOneSpectrumRingOfIntegersRat)) :=
    ((algebraMap (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat))).charZero_iff
      (algebraMap (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat))).injective).mp inferInstance
  -- the transported point of a global torsion class is local torsion
  have hmem : ∀ w : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p,
      (show ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
          (HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat))).Point from
        WeierstrassCurve.Affine.Point.map (W' := E)
          (algClosureEmbeddingRat hp.toHeightOneSpectrumRingOfIntegersRat)
          (show ((E)⁄(AlgebraicClosure ℚ)).Point from w.1)) ∈
      AddSubgroup.torsionBy
        ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
          (HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat))).Point ((p : ℕ) : ℤ) := by
    intro w
    have h1 : ((p : ℕ) : ℤ) •
        (show ((E)⁄(AlgebraicClosure ℚ)).Point from w.1) = 0 := by
      have h0 := w.2
      rw [Submodule.mem_torsionBy_iff] at h0
      exact h0
    show ((p : ℕ) : ℤ) • WeierstrassCurve.Affine.Point.map (W' := E)
        (algClosureEmbeddingRat hp.toHeightOneSpectrumRingOfIntegersRat)
        (show ((E)⁄(AlgebraicClosure ℚ)).Point from w.1) = 0
    rw [← map_zsmul, h1, map_zero]
  -- the transport map on torsion
  let ι : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →
      AddSubgroup.torsionBy
        ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
          (HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat))).Point ((p : ℕ) : ℤ) :=
    fun w => ⟨_, hmem w⟩
  have hιadd : ∀ w₁ w₂, ι (w₁ + w₂) = ι w₁ + ι w₂ := by
    intro w₁ w₂
    apply Subtype.ext
    show WeierstrassCurve.Affine.Point.map (W' := E)
        (algClosureEmbeddingRat hp.toHeightOneSpectrumRingOfIntegersRat)
        ((show ((E)⁄(AlgebraicClosure ℚ)).Point from w₁.1) +
          (show ((E)⁄(AlgebraicClosure ℚ)).Point from w₂.1)) = _
    rw [map_add]
    rfl
  have hιinj : Function.Injective ι := by
    intro a b hab
    have h1 : WeierstrassCurve.Affine.Point.map (W' := E)
        (algClosureEmbeddingRat hp.toHeightOneSpectrumRingOfIntegersRat)
        (show ((E)⁄(AlgebraicClosure ℚ)).Point from a.1) =
        WeierstrassCurve.Affine.Point.map (W' := E)
          (algClosureEmbeddingRat hp.toHeightOneSpectrumRingOfIntegersRat)
          (show ((E)⁄(AlgebraicClosure ℚ)).Point from b.1) :=
      congrArg Subtype.val hab
    apply Subtype.ext
    show (show ((E)⁄(AlgebraicClosure ℚ)).Point from a.1) =
      (show ((E)⁄(AlgebraicClosure ℚ)).Point from b.1)
    exact WeierstrassCurve.Affine.Point.map_injective
      (f := algClosureEmbeddingRat hp.toHeightOneSpectrumRingOfIntegersRat) h1
  -- the `p²`-counts on both sides make the transport bijective
  have hcardG : Nat.card
      ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p) = p ^ 2 :=
    TorsionCard.card_torsionBy (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) p
      (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hcardL : Nat.card (AddSubgroup.torsionBy
      ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat))).Point ((p : ℕ) : ℤ)) =
      p ^ 2 :=
    TorsionCard.card_torsionBy
      ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat))).map
        (algebraMap (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat)
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat)))) p
      (Nat.cast_ne_zero.mpr hp.ne_zero)
  haveI hfinG : Finite ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p) :=
    Nat.finite_of_card_ne_zero (by
      rw [hcardG]
      have := hp.pos
      positivity)
  haveI hfinL : Finite (AddSubgroup.torsionBy
      ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat))).Point ((p : ℕ) : ℤ)) :=
    Nat.finite_of_card_ne_zero (by
      rw [hcardL]
      have := hp.pos
      positivity)
  have hιbij : Function.Bijective ι :=
    (Nat.bijective_iff_injective_and_card ι).mpr
      ⟨hιinj, by rw [hcardG, hcardL]⟩
  -- the pulled-back functional
  let f : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →+ ZMod p :=
    AddMonoidHom.mk' (fun w => π (ι w))
      (fun w₁ w₂ => by rw [hιadd w₁ w₂, map_add])
  haveI : Fintype ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p) :=
    Fintype.ofFinite _
  haveI : Module.Finite (ZMod p)
      ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p) :=
    Module.Finite.of_finite
  have hfr : Module.finrank (ZMod p)
      ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p) = 2 := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod p)
      (V := ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p))
    rw [ZMod.card] at h1
    have h2 : p ^ 2 = p ^ Module.finrank (ZMod p)
        ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p) := by
      rw [← hcardG, Nat.card_eq_fintype_card]
      exact h1
    exact Nat.pow_right_injective hp.two_le h2.symm
  have hrange : LinearMap.range (AddMonoidHom.toZModLinearMap p f) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    obtain ⟨Qc, hQc⟩ := hπsurj c
    obtain ⟨w, hw⟩ := hιbij.2 Qc
    refine ⟨w, ?_⟩
    show π (ι w) = c
    rw [hw]
    exact hQc
  have hrn := LinearMap.finrank_range_add_finrank_ker
    (AddMonoidHom.toZModLinearMap p f)
  rw [hrange, finrank_top, Module.finrank_self, hfr] at hrn
  refine ⟨LinearMap.ker (AddMonoidHom.toZModLinearMap p f), by omega, ?_⟩
  intro σ hσ v
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
    LinearMap.mem_ker, map_sub]
  have hfeq : f (E.galoisRep p hp.pos
      ((Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat))) σ) v) = f v := by
    show π (ι (E.galoisRep p hp.pos
      ((Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat))) σ) v)) = π (ι v)
    refine hπinv σ hσ (ι v) (ι (E.galoisRep p hp.pos
      ((Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat))) σ) v)) ?_
    have hb : (show ((E)⁄(AlgebraicClosure ℚ)).Point from
        (E.galoisRep p hp.pos
          ((Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hp.toHeightOneSpectrumRingOfIntegersRat))) σ) v).1) =
        WeierstrassCurve.Affine.Point.map
          (((Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hp.toHeightOneSpectrumRingOfIntegersRat))) σ :
            AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom
          (show ((E)⁄(AlgebraicClosure ℚ)).Point from v.1) := rfl
    show WeierstrassCurve.Affine.Point.map (W' := E)
        (algClosureEmbeddingRat hp.toHeightOneSpectrumRingOfIntegersRat)
        (show ((E)⁄(AlgebraicClosure ℚ)).Point from
          (E.galoisRep p hp.pos
            ((Field.absoluteGaloisGroup.map (algebraMap ℚ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat))) σ) v).1) = _
    rw [hb]
    rw [point_map_algClosureEmbeddingRat_comm]
    have hbb : ∀ Qp : ((E)⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat))).Point,
        WeierstrassCurve.Affine.Point.map (W' := E)
          (algClosureSigmaRat hp.toHeightOneSpectrumRingOfIntegersRat σ) Qp =
        (show ((E)⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat))).Point from
          WeierstrassCurve.Affine.Point.map
            (W' := E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
              hp.toHeightOneSpectrumRingOfIntegersRat)))
            ((σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat))
              ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat]
              (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat)))).toAlgHom
            (show ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
              hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat))).Point from Qp)) := by
      intro Qp
      cases Qp with
      | zero => rfl
      | some x y h => rfl
    rw [hbb]
  show AddMonoidHom.toZModLinearMap p f (E.galoisRep p hp.pos
      ((Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat))) σ) v) -
      AddMonoidHom.toZModLinearMap p f v = 0
  show f (E.galoisRep p hp.pos
      ((Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat))) σ) v) - f v = 0
  rw [hfeq, sub_self]

open ValuativeRel IsDedekindDomain in
set_option backward.isDefEq.respectTransparency false in
/-- **The Tate étale line at `p`, split multiplicative case** (DERIVED
2026-07-23 from the local Kummer quotient
`exists_localTorsionQuotient_of_split` and the pullback glue
`exists_etale_line_of_localTorsionQuotient`): for an elliptic curve
over `ℚ` whose base change to `ℚ̂_p` has SPLIT multiplicative
reduction, there is a line `L ⊆ E[p]` such that the local inertia at
`p` acts trivially on `E[p]/L`. Content (Silverman ATAEC V.3, V.5):
the Tate uniformization `exists_tateEquivSepClosure` gives a
Galois-equivariant `ℚ̂̄_pˣ/q_Eᶻ ≅ E(ℚ̂̄_p)`; a `p`-torsion class is
represented by `u` with `u^p = q_E^a`
(`exists_rep_pow_eq_zpow_of_torsion`), and for `σ` in the local Galois
group `σ(u)/u ∈ μ_p` since `σ` fixes `q_E` — so with `L` the image of
the `μ_p` classes the quotient action of the WHOLE local Galois group,
in particular of inertia, is trivial; transport to the global torsion
rides the chosen embedding `ℚ̄ ↪ ℚ̂̄_p` as in the unramifiedness glue of
`Semistable.lean`. -/
theorem WeierstrassCurve.exists_etale_line_of_split_multiplicative_self
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : p.Prime)
    [(E.map (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat))).HasSplitMultiplicativeReduction
      𝒪[IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat]] :
    ∃ L : Submodule (ZMod p) ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p),
      Module.finrank (ZMod p) L = 1 ∧
      ∀ σ ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat,
        ∀ v, L.mkQ (E.galoisRep p hp.pos
            ((Field.absoluteGaloisGroup.map (algebraMap ℚ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat))) σ) v) = L.mkQ v := by
  classical
  obtain ⟨π, hπsurj, hπinv⟩ :=
    WeierstrassCurve.exists_localTorsionQuotient_of_split hp
      (E.map (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat))) hp.ne_zero
  exact E.exists_etale_line_of_localTorsionQuotient hp π hπsurj
    (fun σ _ P Q hQ => hπinv
      (σ : (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat))
        ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat]
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat))) P Q hQ)

open ValuativeRel IsDedekindDomain in
set_option backward.isDefEq.respectTransparency false in
/-- **The Tate étale line at `p`, nonsplit multiplicative case**
(DERIVED 2026-07-23 from the local twist-descended quotient
`exists_localTorsionQuotient_of_nonsplit` and the pullback glue
`exists_etale_line_of_localTorsionQuotient`): for an elliptic curve
over `ℚ` with multiplicative reduction at `p` whose completed base
change is NOT split, the étale-quotient line still exists. Content:
the quadratic twist by the unramified quadratic extension of `ℚ̂_p`
(`exists_quadraticTwist_hasSplitMultiplicativeReduction`) has split
multiplicative reduction and the same `j`-invariant; the twist
character is unramified at `p`, so the two mod-`p` INERTIA modules are
isomorphic, and the line of the split case transfers. Silverman ATAEC
V.5.4; Serre Duke 1987, §4.1. -/
theorem WeierstrassCurve.exists_etale_line_of_nonsplit_multiplicative_self
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : p.Prime)
    [E.HasMultiplicativeReduction
      (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)]
    (hns : ¬ (E.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat))).HasSplitMultiplicativeReduction
      𝒪[IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat]) :
    ∃ L : Submodule (ZMod p) ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p),
      Module.finrank (ZMod p) L = 1 ∧
      ∀ σ ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat,
        ∀ v, L.mkQ (E.galoisRep p hp.pos
            ((Field.absoluteGaloisGroup.map (algebraMap ℚ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat))) σ) v) = L.mkQ v := by
  classical
  haveI := hasMultiplicativeReduction_adicCompletion hp E
  obtain ⟨π, hπsurj, hπinv⟩ :=
    WeierstrassCurve.exists_localTorsionQuotient_of_nonsplit hp
      (E.map (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat))) hns hp.ne_zero
  exact E.exists_etale_line_of_localTorsionQuotient hp π hπsurj hπinv

open ValuativeRel IsDedekindDomain in
set_option backward.isDefEq.respectTransparency false in
/-- **The Tate étale line at `p`, multiplicative case** (DERIVED
2026-07-22 from the split leaf
`exists_etale_line_of_split_multiplicative_self` and the nonsplit
twist leaf `exists_etale_line_of_nonsplit_multiplicative_self`, by the
split/nonsplit case split on the completed base change): for an
elliptic curve over `ℚ` with multiplicative reduction at `p`, there is
a line `L ⊆ E[p]` such that the local inertia at `p` acts trivially on
`E[p]/L`. Silverman ATAEC V.3, V.5. -/
theorem WeierstrassCurve.exists_etale_line_of_multiplicative_self
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : p.Prime)
    [E.HasMultiplicativeReduction
      (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)] :
    ∃ L : Submodule (ZMod p) ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p),
      Module.finrank (ZMod p) L = 1 ∧
      ∀ σ ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat,
        ∀ v, L.mkQ (E.galoisRep p hp.pos
            ((Field.absoluteGaloisGroup.map (algebraMap ℚ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat))) σ) v) = L.mkQ v := by
  classical
  haveI := hasMultiplicativeReduction_adicCompletion hp E
  by_cases hsp : (E.map (algebraMap ℚ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat))).HasSplitMultiplicativeReduction
      𝒪[IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat]
  · haveI := hsp
    exact E.exists_etale_line_of_split_multiplicative_self hp
  · exact E.exists_etale_line_of_nonsplit_multiplicative_self hp hsp

/-- A classical decidable-equality instance on the algebraic closure of
the residue field at a finite place of `ℚ`, mirroring
`instDecidableEqAlgClosureAdicCompletionRat` in `Semistable.lean`
(needed for the group law on the points of the reduced curve, used to
state the ordinary/supersingular dichotomy below). -/
noncomputable instance instDecidableEqAlgClosureResidueFieldAtPrimeRat
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    DecidableEq (AlgebraicClosure
      (IsLocalRing.ResidueField (Localization.AtPrime v.asIdeal))) :=
  Classical.typeDecidableEq _

open ValuativeRel IsDedekindDomain in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
/-- **The local reduction datum at a good prime** (sorry node, cut
2026-07-25 out of `exists_localReductionAddHom_of_good_reduction` — the
RESIDUE-FIELD half): for an elliptic curve over `ℚ` with good reduction
at `p`, there is a LOCAL ring homomorphism `ρ` from the valuation
subring `𝒪 = localValuationSubring v` of `ℚ̄_p` (the integral closure of
`ℤ_p`) to the algebraic closure of the residue field `𝔽_p =
IsLocalRing.ResidueField (Localization.AtPrime v.asIdeal)`, along which
the base-changed curve `E/ℚ̄_p` reduces to the base-changed reduced
curve `Ẽ/𝔽̄_p`, and the reduced curve is nonsingular (`Δ ≠ 0`).

Content: (1) `IsLocalRing.ResidueField 𝒪` is an ALGEBRAIC CLOSURE of
`𝔽_p` — `𝒪` is the integral closure of the complete DVR `𝒪ᵥ` in an
algebraic closure of its fraction field, so its residue field is
algebraic over `𝔽_p` and algebraically closed — hence isomorphic (as an
`𝔽_p`-algebra) to `AlgebraicClosure 𝔽_p`; composing the residue map
`𝒪 → ResidueField 𝒪` with that isomorphism gives `ρ`, and the residue
map of a local ring is a local homomorphism.  (2) The five coefficients
of `E/ℚ̄_p` are integral over `ℤ_p` and reduce to the coefficients of
`Ẽ` — this is the `(𝒪, h𝒪)` pattern of
`WeierstrassCurve.baseChange_coeff_mem` in
`Fermat.FLT.KnownIn1980s.EllipticCurves.Flat`, applied to the minimal
integral model that defines `E.reduction`.  (3) `Δ̄ ≠ 0` is exactly good
reduction (`hasGoodReduction_iff_isElliptic_reduction`), transported
along the base change to `𝔽̄_p`.

Once this datum is in hand, the reduction map itself, its additivity
and its kernel are supplied — PROVEN, characteristic-free, with no
formal groups — by `WeierstrassCurve.IsReductionAlong.redHom` and
`redFun_eq_zero_iff` in
`Fermat.FLT.KnownIn1980s.EllipticCurves.PointReduction`. -/
theorem WeierstrassCurve.exists_localReductionDatum_of_good_reduction
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : p.Prime)
    [E.HasGoodReduction
      (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)] :
    ∃ ρ : (localValuationSubring hp.toHeightOneSpectrumRingOfIntegersRat) →+*
        AlgebraicClosure (IsLocalRing.ResidueField
          (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)),
      IsLocalHom ρ ∧
      WeierstrassCurve.IsReductionAlong
        (localValuationSubring hp.toHeightOneSpectrumRingOfIntegersRat) ρ
        ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
          (HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat)))
        ((E.reduction
          (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal))⁄
          (AlgebraicClosure (IsLocalRing.ResidueField
            (Localization.AtPrime
              hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)))) ∧
      ((E.reduction
        (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal))⁄
        (AlgebraicClosure (IsLocalRing.ResidueField
          (Localization.AtPrime
            hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)))).Δ ≠ 0 :=
  sorry

open ValuativeRel IsDedekindDomain in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
/-- **Reduction is surjective onto the geometric points of `Ẽ`** (sorry
node, cut 2026-07-25 out of `exists_localReductionAddHom_of_good_reduction`
— the HENSEL half): given the local reduction datum of
`exists_localReductionDatum_of_good_reduction`, the point-reduction
homomorphism `redHom` is onto `Ẽ(𝔽̄_p)`.

Content (Silverman *AEC* VII.2.1, VII.3.1): the valuation subring
`𝒪 = localValuationSubring v` of `ℚ̄_p` is HENSELIAN — it is the
integral closure of the complete DVR `𝒪ᵥ` in an algebraic extension,
so every finite `𝒪`-algebra is a product of local rings — and its
residue field is algebraically closed.  Given `(x̄, ȳ)` on `Ẽ`, lift
`x̄` to some `x ∈ 𝒪` and solve the Weierstrass equation for `y` over
`x`: the monic quadratic `Y² + (a₁x + a₃)Y − (x³ + a₂x² + a₄x + a₆)`
has `ȳ` as a residue root, and either that root is simple — Hensel
lifts it — or the reduced point is `2`-torsion, in which case the
`x`-direction derivative is a unit (`Wred.Δ ≠ 0`, exactly
`IsReductionAlong.res_tangentNum_ne_zero`) and one instead lifts along
`x`.  The point at infinity is the image of the point at infinity. -/
theorem WeierstrassCurve.localReduction_surjective_of_good_reduction
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : p.Prime)
    [E.HasGoodReduction
      (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)]
    (ρ : (localValuationSubring hp.toHeightOneSpectrumRingOfIntegersRat) →+*
      AlgebraicClosure (IsLocalRing.ResidueField
        (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)))
    [IsLocalHom ρ]
    (hred : WeierstrassCurve.IsReductionAlong
      (localValuationSubring hp.toHeightOneSpectrumRingOfIntegersRat) ρ
      ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat)))
      ((E.reduction
        (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal))⁄
        (AlgebraicClosure (IsLocalRing.ResidueField
          (Localization.AtPrime
            hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)))))
    (hΔ : ((E.reduction
      (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal))⁄
      (AlgebraicClosure (IsLocalRing.ResidueField
        (Localization.AtPrime
          hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)))).Δ ≠ 0) :
    Function.Surjective (hred.redHom hΔ) :=
  sorry

open ValuativeRel IsDedekindDomain in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
/-- **Reduction is invariant under the local inertia** (sorry node, cut
2026-07-25 out of `exists_localReductionAddHom_of_good_reduction` — the
INERTIA half): given the local reduction datum of
`exists_localReductionDatum_of_good_reduction`, the point-reduction
homomorphism is unchanged by transporting a point along any `σ` in
`localInertiaGroup v`.

Content: `localInertiaGroup v` is by DEFINITION
`AddSubgroup.inertia` of the maximal ideal of the integral closure
`𝒪 = localValuationSubring v`, i.e. the subgroup of
`Gal(ℚ̄_p/ℚ_p)` acting trivially on `𝒪/𝔪` — see
`AbsoluteGaloisGroup.residue_apply_eq_of_mem_localInertiaGroup`.  Each
such `σ` preserves `𝒪` (`mem_decompositionSubgroup_localValuationSubring`),
so it maps an integral point to an integral point and a non-integral
one to a non-integral one, and on integral coordinates it acts
trivially after reduction; hence `red (σ · P) = red P` coordinate by
coordinate.  NOTE the quantifier: this is an INERTIA-only statement and
is FALSE for a general element of the decomposition group — Frobenius
acts on `𝔽̄_p` by `x ↦ x^p`, which moves the reduced point. -/
theorem WeierstrassCurve.localReduction_inertia_invariant_of_good_reduction
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : p.Prime)
    [E.HasGoodReduction
      (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)]
    (ρ : (localValuationSubring hp.toHeightOneSpectrumRingOfIntegersRat) →+*
      AlgebraicClosure (IsLocalRing.ResidueField
        (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)))
    [IsLocalHom ρ]
    (hred : WeierstrassCurve.IsReductionAlong
      (localValuationSubring hp.toHeightOneSpectrumRingOfIntegersRat) ρ
      ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat)))
      ((E.reduction
        (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal))⁄
        (AlgebraicClosure (IsLocalRing.ResidueField
          (Localization.AtPrime
            hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)))))
    (hΔ : ((E.reduction
      (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal))⁄
      (AlgebraicClosure (IsLocalRing.ResidueField
        (Localization.AtPrime
          hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)))).Δ ≠ 0) :
    ∀ σ ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat,
      ∀ P : ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
          (HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat))).Point,
        (hred.redHom hΔ) (WeierstrassCurve.Affine.Point.map
          (W' := E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat)))
          ((σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hp.toHeightOneSpectrumRingOfIntegersRat))
            ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
              hp.toHeightOneSpectrumRingOfIntegersRat]
            (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hp.toHeightOneSpectrumRingOfIntegersRat)))).toAlgHom P)
          = (hred.redHom hΔ) P :=
  sorry

open ValuativeRel IsDedekindDomain in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
/-- **The reduction homomorphism on ALL local points at a good prime**
(PROVEN 2026-07-25 over three named leaves —
`exists_localReductionDatum_of_good_reduction` (residue field),
`localReduction_surjective_of_good_reduction` (Hensel) and
`localReduction_inertia_invariant_of_good_reduction` (inertia) — on top
of the reduction-of-POINTS theory built in
`Fermat.FLT.KnownIn1980s.EllipticCurves.PointReduction`, which supplies
the map itself, its ADDITIVITY and its KERNEL, all proven: mathlib's
`Reduction.lean` reduces the CURVE, not its points, so
`WeierstrassCurve.IsReductionAlong` / `IsReductionAlong.redHom` /
`IsReductionAlong.redFun_eq_zero_iff` are new theory.  The third clause
of this statement is discharged outright by `redFun_eq_zero_iff`; cut
2026-07-25 out of `exists_localReductionHom_of_good_reduction` — the
GEOMETRY half of that leaf): for an elliptic curve over `ℚ` with good
reduction at `p`,
the points of the base change to the algebraic closure `ℚ̄_p` of the
completion reduce to the geometric points of `Ẽ/𝔽̄_p` by a group
homomorphism `red` which

* is SURJECTIVE onto all of `Ẽ(𝔽̄_p)` — the valuation ring `𝒪` of
  `ℚ̄_p` (`localValuationSubring`, the integral closure of `ℤ_p`) is
  henselian with algebraically closed residue field and `Ẽ` is smooth,
  so every geometric point of `Ẽ` lifts (Silverman *AEC* VII.2.1 for
  the map, VII.3.1 / Hensel for the lift);
* is invariant under the local INERTIA — inertia is by definition the
  subgroup of `Gal(ℚ̄_p/ℚ_p)` acting trivially on the residue field of
  `𝒪` (`localInertiaGroup` is `AddSubgroup.inertia` of the maximal
  ideal of the integral closure), and reduction is by construction
  computed in that residue field;
* has kernel exactly the NON-INTEGRAL locus: an affine point
  `(x, y)` reduces to `O` iff `x ∉ 𝒪`. This is Silverman *AEC* VII.2.2:
  `v x < 0` forces `v y < v x < 0` and the point lies in the formal
  group `Ê(𝔪)`, i.e. in `E₁`; conversely an integral abscissa forces an
  integral ordinate and an affine reduced point, which is never `O`.

The intrinsic (map-free) description of the kernel is what lets the
`p`-divisibility of `E₁` be stated and owned SEPARATELY, in
`exists_localKernelDivision_of_good_reduction` below; the two are
assembled into `exists_localReductionHom_of_good_reduction` by the
lift-and-correct argument.

Supply line: `Fermat/FLT/KnownIn1980s/EllipticCurves/GoodReduction.lean`
(`ValuationSubring.mem_of_root_of_inv_leadingCoeff_mem`, `RtoO`,
`isLocalHom_RtoO`, `torsion_abscissa_mem`, `torsion_ordinate_mem`) and
`Flat.lean` (`baseChange_coeff_mem`, `kernel_add_abscissa_notMem`,
`kernel_sub_abscissa_notMem_of_residue_eq`, `val_abscissa_lt_val_ordinate`)
already run the `(𝒪 : ValuationSubring _, h𝒪)` pattern used here, with
`𝒪 = localValuationSubring v`. The missing analytic input is the
comparison of residue fields: `IsLocalRing.ResidueField 𝒪` is an
algebraic closure of `IsLocalRing.ResidueField (Localization.AtPrime
v.asIdeal) = 𝔽_p`, so it is isomorphic to the `AlgebraicClosure` used
in the statement. -/
theorem WeierstrassCurve.exists_localReductionAddHom_of_good_reduction
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : p.Prime)
    [E.HasGoodReduction
      (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)] :
    ∃ red : ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat))).Point →+
        ((E.reduction
          (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal))⁄
          (AlgebraicClosure (IsLocalRing.ResidueField
            (Localization.AtPrime
              hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)))).Point,
      Function.Surjective red ∧
      (∀ σ ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat,
        ∀ P : ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
            (HeightOneSpectrum.adicCompletion ℚ
              hp.toHeightOneSpectrumRingOfIntegersRat))).Point,
          red (WeierstrassCurve.Affine.Point.map
            (W' := E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
              hp.toHeightOneSpectrumRingOfIntegersRat)))
            ((σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat))
              ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat]
              (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat)))).toAlgHom P) = red P) ∧
      (∀ (x y : AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat))
          (h : ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
            (HeightOneSpectrum.adicCompletion ℚ
              hp.toHeightOneSpectrumRingOfIntegersRat))).toAffine.Nonsingular x y),
        red (WeierstrassCurve.Affine.Point.some x y h) = 0 ↔
          x ∉ localValuationSubring hp.toHeightOneSpectrumRingOfIntegersRat) := by
  classical
  obtain ⟨ρ, hlocal, hred, hΔ⟩ := E.exists_localReductionDatum_of_good_reduction hp
  haveI := hlocal
  exact ⟨hred.redHom hΔ,
    E.localReduction_surjective_of_good_reduction hp ρ hred hΔ,
    E.localReduction_inertia_invariant_of_good_reduction hp ρ hred hΔ,
    fun _ _ hxy => hred.redFun_eq_zero_iff hΔ hxy⟩

/-- **`ΨSqₙ ≠ 0` for an elliptic curve over ANY field**, with no
characteristic hypothesis (PROVEN 2026-07-25, an input of the
`p`-divisibility of the kernel of reduction below). Mathlib's
`WeierstrassCurve.ΨSq_ne_zero` needs `(n : R) ≠ 0`, which is exactly
what FAILS in the application: there `n = p` and the base is the
residue field of characteristic `p`. The characteristic-free proof
instead uses the Bézout relation `A · Φₙ + B · Ψ²ₙ = 1`
(`isCoprime_Φ_ΨSq`, available because `Δ` is a unit): if `Ψ²ₙ = 0`
then `Φₙ` is a unit, hence of degree `0`, contradicting
`natDegree_Φ n = n.natAbs ^ 2 ≠ 0`. -/
theorem WeierstrassCurve.ΨSq_ne_zero_of_isElliptic {L : Type*} [Field L]
    (W : WeierstrassCurve L) [W.IsElliptic] {n : ℤ} (hn : n ≠ 0) :
    W.ΨSq n ≠ 0 := by
  intro h0
  obtain ⟨A, _B, hAB⟩ := WeierstrassCurve.isCoprime_Φ_ΨSq W hn W.isUnit_Δ
  rw [h0, mul_zero, add_zero] at hAB
  have hu : IsUnit (W.Φ n) := IsUnit.of_mul_eq_one_right A hAB
  have hdeg : (W.Φ n).natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
  rw [WeierstrassCurve.natDegree_Φ] at hdeg
  exact hn (Int.natAbs_eq_zero.mp (by simpa using hdeg))

/-- **The arithmetic input of the division argument: at good reduction
the `n`-division data is integral, and `Ψ²ₙ` has a UNIT coefficient**
(PROVEN 2026-07-25). Along any ring map `ψ : K → L` carrying the
good-reduction model `R ⊆ K` into a subring `𝒪 ⊆ L`:

* every coefficient of `Φₙ` of the base-changed curve lies in `𝒪` —
  because `E.map ψ = (integralModel R E).map φ`, so those coefficients
  are images of coefficients of `Φₙ` over `R`;
* some coefficient of `Ψ²ₙ` becomes a UNIT of `𝒪` — because the
  reduction `Ẽ/k` is again elliptic, so `Ψ²ₙ(Ẽ) ≠ 0` by
  `ΨSq_ne_zero_of_isElliptic` (no characteristic hypothesis, and this
  is where it is needed: `k` has characteristic `p` and `n = p`), so
  some coefficient of `Ψ²ₙ` over `R` survives reduction, i.e. avoids
  the maximal ideal, i.e. is a unit of the local ring `R`.

The second bullet is the whole arithmetic content of the argument: it
is what forces the auxiliary polynomial `Φₙ − x · Ψ²ₙ` to have a
NON-INTEGRAL root once `x` is non-integral. -/
theorem WeierstrassCurve.coeff_Φ_mem_and_isUnit_coeff_ΨSq_of_hasGoodReduction
    {R K L : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field L]
    (E : WeierstrassCurve K) [E.HasGoodReduction R]
    (ψ : K →+* L) (𝒪 : Subring L)
    (hφmem : ∀ r : R, ψ (algebraMap R K r) ∈ 𝒪)
    {n : ℤ} (hn : n ≠ 0) :
    (∀ i : ℕ, ((E.map ψ).Φ n).coeff i ∈ 𝒪) ∧
      ∃ (j : ℕ) (c : L), c ∈ 𝒪 ∧ c * ((E.map ψ).ΨSq n).coeff j = 1 := by
  classical
  set φ : R →+* L := ψ.comp (algebraMap R K)
  have hmap : E.map ψ = (integralModel R E).map φ := by
    conv_lhs => rw [← WeierstrassCurve.baseChange_integralModel_eq R E]
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
  refine ⟨fun i => ?_, ?_⟩
  · rw [hmap, WeierstrassCurve.map_Φ, Polynomial.coeff_map]
    exact hφmem _
  · haveI : (E.reduction R).IsElliptic :=
      (WeierstrassCurve.hasGoodReduction_iff_isElliptic_reduction R).mp inferInstance
    have hne : (E.reduction R).ΨSq n ≠ 0 :=
      WeierstrassCurve.ΨSq_ne_zero_of_isElliptic _ hn
    rw [WeierstrassCurve.reduction, WeierstrassCurve.map_ΨSq] at hne
    obtain ⟨j, hj⟩ : ∃ j : ℕ,
        (((integralModel R E).ΨSq n).map (IsLocalRing.residue R)).coeff j ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hne (Polynomial.ext fun j => by simpa using hc j)
    rw [Polynomial.coeff_map] at hj
    have hu : IsUnit (((integralModel R E).ΨSq n).coeff j) :=
      IsLocalRing.notMem_maximalIdeal.mp fun hm =>
        hj ((IsLocalRing.residue_eq_zero_iff _).mpr hm)
    refine ⟨j, φ ((hu.unit⁻¹ : Rˣ) : R), hφmem _, ?_⟩
    rw [hmap, WeierstrassCurve.map_ΨSq, Polynomial.coeff_map, ← map_mul,
      hu.val_inv_mul, map_one]

open Polynomial in
/-- **The division step, over an ALGEBRAICALLY CLOSED field: a
non-integral abscissa is `n` times a non-integral abscissa** (PROVEN
2026-07-25). This is the geometric core of the `p`-divisibility of the
kernel of reduction, and it is a DIVISION-POLYNOMIAL argument rather
than a formal-group one.

Given the two integrality facts of
`coeff_Φ_mem_and_isUnit_coeff_ΨSq_of_hasGoodReduction`, consider the
monic polynomial `F = Φₙ − x · Ψ²ₙ`, monic of degree `n²` because
`deg Φₙ = n² > deg Ψ²ₙ`. Its roots are exactly the abscissae `r` with
`x([n](r, ·)) = x`.

* `F` has a root OUTSIDE `𝒪`. Otherwise all roots lie in `𝒪`, so (the
  field being algebraically closed and `F` monic) all COEFFICIENTS of
  `F` lie in `𝒪`; taking the coefficient `j` at which `Ψ²ₙ` is a unit
  of `𝒪` gives `x · (Ψ²ₙ)ⱼ = (Φₙ)ⱼ − Fⱼ ∈ 𝒪`, hence `x ∈ 𝒪` — against
  the hypothesis. Note this is where the non-integrality of `x` is
  CONSUMED, and it is what makes the argument non-circular.
* At such a root, `Ψ²ₙ(r) ≠ 0`: otherwise `Φₙ(r) = 0` too, against
  `isCoprime_Φ_ΨSq`.
* The field being algebraically closed, the quadratic `yQuad` has a
  root `y₀`, giving a point `(r, y₀)` on the curve; the multiplication
  formula `TorsionCard.exists_smul_some_eq` then gives
  `n • (r, y₀) = (x', y')` with `x' · Ψ²ₙ(r) = Φₙ(r) = x · Ψ²ₙ(r)`, so
  `x' = x` and `n • (r, y₀) = ±(x, y)`; replacing `y₀` by `negY r y₀`
  in the minus case finishes.

**Why not the formal group.** The route first mapped for this node was
analytic — Weierstrass preparation and the Newton polygon of
`[p](T) = pT + ⋯ + (unit) T^{p^h}` over `ℂ_p` — because the naive
"pick any `Q` with `pQ = P`, then correct by a `p`-torsion point"
presupposes the surjectivity of reduction on `E[p]`, which is what the
parent node is proving. The argument here avoids BOTH: it never picks
an arbitrary preimage (it picks a root of an explicit polynomial and
proves that root non-integral), and it needs no completeness — only
that the field is algebraically closed. -/
theorem WeierstrassCurve.exists_zsmul_eq_of_abscissa_notMem
    {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L]
    (W : WeierstrassCurve L) [W.IsElliptic] (𝒪 : ValuationSubring L)
    {n : ℤ} (hn : n ≠ 0)
    (hΦmem : ∀ i, (W.Φ n).coeff i ∈ 𝒪)
    (hunit : ∃ (j : ℕ) (c : L), c ∈ 𝒪 ∧ c * (W.ΨSq n).coeff j = 1)
    {x y : L} (h : W.toAffine.Nonsingular x y) (hx : x ∉ 𝒪) :
    ∃ (x' y' : L) (h' : W.toAffine.Nonsingular x' y'),
      x' ∉ 𝒪 ∧
      n • (Affine.Point.some x' y' h' : W.toAffine.Point) =
        Affine.Point.some x y h := by
  classical
  have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ zero_mem 𝒪)
  set F : L[X] := W.Φ n - C x * W.ΨSq n with hF
  have hΦmonic : (W.Φ n).Monic := W.leadingCoeff_Φ n
  have hdegnat : (C x * W.ΨSq n).natDegree < (W.Φ n).natDegree := by
    rw [Polynomial.natDegree_C_mul hx0, WeierstrassCurve.natDegree_Φ]
    have h1 : (W.ΨSq n).natDegree ≤ n.natAbs ^ 2 - 1 := W.natDegree_ΨSq_le n
    have h2 : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
    have h3 : 1 ≤ n.natAbs ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hFmonic : F.Monic :=
    hΦmonic.sub_of_left (Polynomial.degree_lt_degree hdegnat)
  have hsplits : F.Splits := IsAlgClosed.splits F
  have hex : ∃ r ∈ F.roots, r ∉ 𝒪 := by
    by_contra hall
    push Not at hall
    have hlift : F ∈ Polynomial.lifts (𝒪.toSubring.subtype) :=
      hsplits.mem_lift_of_roots_mem_range hFmonic _
        fun a ha => ⟨⟨a, hall a ha⟩, rfl⟩
    have hcoeff : ∀ i, F.coeff i ∈ 𝒪 := by
      intro i
      obtain ⟨z, hz⟩ := (Polynomial.lifts_iff_coeff_lifts F).mp hlift i
      exact hz ▸ z.2
    obtain ⟨j, c, hc, hcj⟩ := hunit
    have hFj : F.coeff j = (W.Φ n).coeff j - x * (W.ΨSq n).coeff j := by
      rw [hF, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    have hxc : x * (W.ΨSq n).coeff j ∈ 𝒪 := by
      have hsub := sub_mem (hΦmem j) (hcoeff j)
      rwa [hFj, sub_sub_cancel] at hsub
    refine hx ?_
    have hxeq : x = (x * (W.ΨSq n).coeff j) * c := by
      rw [mul_assoc, mul_comm ((W.ΨSq n).coeff j) c, hcj, mul_one]
    rw [hxeq]
    exact mul_mem hxc hc
  obtain ⟨r, hrroot, hr⟩ := hex
  have hFr : F.eval r = 0 := (Polynomial.mem_roots hFmonic.ne_zero).mp hrroot
  have hkey : (W.Φ n).eval r = x * (W.ΨSq n).eval r := by
    have h0 : (W.Φ n).eval r - x * (W.ΨSq n).eval r = 0 := by
      simpa [hF] using hFr
    exact sub_eq_zero.mp h0
  have hΨr : (W.ΨSq n).eval r ≠ 0 := by
    intro h0
    have hΦr : (W.Φ n).eval r = 0 := by rw [hkey, h0, mul_zero]
    obtain ⟨A, B, hAB⟩ := WeierstrassCurve.isCoprime_Φ_ΨSq W hn W.isUnit_Δ
    have hev := congrArg (Polynomial.eval r) hAB
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
      hΦr, h0, mul_zero, add_zero] at hev
    exact zero_ne_one hev
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : L, (TorsionCard.yQuad W r).eval y₀ = 0 := by
    have hdeg2 : (TorsionCard.yQuad W r).degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree (TorsionCard.yQuad_ne_zero W r),
        TorsionCard.yQuad_natDegree]
      simp
    exact IsAlgClosed.exists_root _ hdeg2
  have heq0 : W.toAffine.Equation r y₀ :=
    (TorsionCard.eval_yQuad_eq_zero_iff_equation W r y₀).mp hy₀
  have h₀ : W.toAffine.Nonsingular r y₀ :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp heq0
  obtain ⟨x', y', h'', hsmul0, hxf0⟩ := TorsionCard.exists_smul_some_eq W hn h₀ hΨr
  have h' : W.toAffine.Nonsingular x' y' := h''
  have hxf : x' * (W.ΨSq n).eval r = (W.Φ n).eval r := hxf0
  have hsmul : n • (Affine.Point.some r y₀ h₀ : W.toAffine.Point) =
      Affine.Point.some x' y' h' := hsmul0
  have hx'x : x' = x := by
    rw [hkey] at hxf
    exact mul_right_cancel₀ hΨr hxf
  subst hx'x
  rcases TorsionCard.eq_or_add_eq_zero_of_X_eq W h' h rfl with heq0' | hneg0
  · have heq : (Affine.Point.some x' y' h' : W.toAffine.Point) =
        Affine.Point.some x' y h := heq0'
    exact ⟨r, y₀, h₀, hr, by rw [hsmul, heq]⟩
  · have hneg : (Affine.Point.some x' y' h' : W.toAffine.Point) +
        Affine.Point.some x' y h = 0 := hneg0
    refine ⟨r, W.toAffine.negY r y₀, (Affine.nonsingular_neg ..).mpr h₀, hr, ?_⟩
    have hopp : (Affine.Point.some x' y' h' : W.toAffine.Point) =
        -(Affine.Point.some x' y h : W.toAffine.Point) :=
      eq_neg_of_add_eq_zero_left hneg
    rw [← Affine.Point.neg_some h₀, smul_neg, hsmul, hopp, neg_neg]

open IsDedekindDomain in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **`ℤ_(p) ⊆ ℚ` lands in the local valuation subring of `ℚ̄_p`**
(PROVEN 2026-07-25, the `hφmem` hypothesis of
`coeff_Φ_mem_and_isUnit_coeff_ΨSq_of_hasGoodReduction` at the place
`v_p`): an element `r` of the good-reduction model
`Localization.AtPrime v_p ⊆ ℚ` has `v_p`-adic valuation `≤ 1` — write
`r = a/s` with `s ∉ v_p`, so `v(s) = 1` by
`intValuation_eq_one_iff_mem_primeCompl` and `v(r) = v(a) ≤ 1` — hence
its image in `ℚ_p` lies in `ℤ_p`, hence its image in `ℚ̄_p` is integral
over `ℤ_p`, i.e. lies in `localValuationSubring v_p`
(`algebraMap_mem_localValuationSubring_of_integer` of
`Semistable.lean`). -/
theorem mem_localValuationSubring_of_algebraMap_localizationAtPrime
    {p : ℕ} (hp : p.Prime)
    (r : Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal) :
    (algebraMap (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)))
      ((algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat))
        (algebraMap
          (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ℚ r)) ∈
      localValuationSubring hp.toHeightOneSpectrumRingOfIntegersRat := by
  refine algebraMap_mem_localValuationSubring_of_integer hp _ ?_
  rw [HeightOneSpectrum.mem_adicCompletionIntegers,
    valued_algebraMap_adicCompletion_eq hp]
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq
    hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal.primeCompl r
  have h2 := congrArg
    (algebraMap (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ℚ)
    (IsLocalization.mk'_spec
      (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal) a s)
  rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h2
  have h3 := congrArg (hp.toHeightOneSpectrumRingOfIntegersRat.valuation ℚ) h2
  have hs1 : hp.toHeightOneSpectrumRingOfIntegersRat.valuation ℚ
      (algebraMap (NumberField.RingOfIntegers ℚ) ℚ
        (s : NumberField.RingOfIntegers ℚ)) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl _ _).mpr s.2
  rw [map_mul, hs1, mul_one] at h3
  rw [h3]
  exact HeightOneSpectrum.valuation_le_one _ a

open ValuativeRel IsDedekindDomain in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
/-- **The kernel of reduction is `p`-divisible over `ℚ̄_p`** (PROVEN
2026-07-25 by a DIVISION-POLYNOMIAL argument; cut 2026-07-25 out of
`exists_localReductionHom_of_good_reduction` — the FORMAL-GROUP half):
every affine point of `E(ℚ̄_p)` whose
abscissa is not integral for the valuation subring
`localValuationSubring` — equivalently, every nonzero point of the
kernel of reduction `E₁(ℚ̄_p) = Ê(𝔪)` — is `p` times another point of
the same kernel.

Mathematically this is the `p`-divisibility of the formal group
`Ê(𝔪)` over the valuation ring of `ℚ̄_p`. Over a FINITE extension of
`ℚ_p` it is FALSE (`Ê(𝔪)` is then a finitely generated `ℤ_p`-module of
positive rank plus finite torsion); it becomes true over `ℚ̄_p`.

**The proof taken is not the formal-group one.** The route originally
mapped was analytic: Weierstrass preparation and the Newton polygon of
`[p](T) = pT + ⋯ + (unit) T^{p^h} + ⋯` over a complete base
(Silverman *AEC* IV.2–IV.3, VII.2, VII.6; ATAEC IV.6). The proof
below is instead a three-line DIVISION-POLYNOMIAL argument, needing no
completeness at all — only that `ℚ̄_p` is algebraically closed and
that `E` has good reduction:

1. `coeff_Φ_mem_and_isUnit_coeff_ΨSq_of_hasGoodReduction` — good
   reduction makes every coefficient of `Φ_p` integral and SOME
   coefficient of `Ψ²_p` a unit (the reduced curve is elliptic, so its
   `Ψ²_p` is nonzero — which needs the characteristic-free
   `ΨSq_ne_zero_of_isElliptic`, since `char = p` here);
2. `mem_localValuationSubring_of_algebraMap_localizationAtPrime` —
   the model `ℤ_(p) ⊆ ℚ` does land in `localValuationSubring`;
3. `exists_zsmul_eq_of_abscissa_notMem` — over an algebraically closed
   field, `F = Φ_p − x · Ψ²_p` is monic of degree `p²`, and if all its
   roots were integral so would all its coefficients be, forcing
   `x ∈ 𝒪` through the unit coefficient of `Ψ²_p`. So some root `r` is
   NON-integral, and any curve point above `r` is a `p`-division point
   of `(x, y)` lying again in the kernel.

Note this also settles the circularity that blocked the obvious
approach: one does not pick an arbitrary `Q` with `pQ = P` and correct
it by a `p`-torsion point (which would presuppose the surjectivity of
reduction on `E[p]` that the parent node is proving) — the division
point is produced as an explicit root and proved non-integral
directly. The `Flat.lean` valuation lemmas
(`kernel_add_abscissa_notMem`, `val_abscissa_lt_val_ordinate`) are
correspondingly NOT needed.

Stated intrinsically — with no reference to a reduction map —
precisely so that this leaf and
`exists_localReductionAddHom_of_good_reduction` can be owned
independently. -/
theorem WeierstrassCurve.exists_localKernelDivision_of_good_reduction
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : p.Prime)
    [E.HasGoodReduction
      (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)]
    (x y : AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hp.toHeightOneSpectrumRingOfIntegersRat))
    (h : ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
      (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat))).toAffine.Nonsingular x y)
    (hx : x ∉ localValuationSubring hp.toHeightOneSpectrumRingOfIntegersRat) :
    ∃ (x' y' : AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat))
        (h' : ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
          (HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat))).toAffine.Nonsingular x' y'),
      x' ∉ localValuationSubring hp.toHeightOneSpectrumRingOfIntegersRat ∧
      ((p : ℕ) : ℤ) • (WeierstrassCurve.Affine.Point.some x' y' h' :
          ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
            (HeightOneSpectrum.adicCompletion ℚ
              hp.toHeightOneSpectrumRingOfIntegersRat))).Point) =
        WeierstrassCurve.Affine.Point.some x y h := by
  classical
  have hn : ((p : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨hΦmem, hunit⟩ :=
    WeierstrassCurve.coeff_Φ_mem_and_isUnit_coeff_ΨSq_of_hasGoodReduction
      (R := Localization.AtPrime
        hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal) E
      ((algebraMap (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat)
        (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat))).comp
        (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat)))
      (localValuationSubring hp.toHeightOneSpectrumRingOfIntegersRat).toSubring
      (fun r => mem_localValuationSubring_of_algebraMap_localizationAtPrime hp r) hn
  exact WeierstrassCurve.exists_zsmul_eq_of_abscissa_notMem _ _ hn hΦmem hunit h hx

open ValuativeRel IsDedekindDomain in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
/-- **The local reduction homomorphism on the `p`-torsion at a good
prime** (DERIVED 2026-07-25 from the two bricks
`exists_localReductionAddHom_of_good_reduction` (the reduction map on
ALL points: surjective, inertia-invariant, kernel = the non-integral
locus) and `exists_localKernelDivision_of_good_reduction` (that kernel
is `p`-divisible); it was cut 2026-07-25 out of
`exists_localTorsionQuotient_of_good_ordinary` as the first of the two
bricks of the ordinary case, and the one carrying the *geometry*): for
an elliptic curve over `ℚ` with good reduction at `p`, the `p`-torsion
of the completed base change over the local algebraic closure maps to
the geometric points of the reduced curve `Ẽ/𝔽̄_p` by a group
homomorphism `red` which

* is invariant under the local INERTIA: inertia is by definition the
  subgroup acting trivially on the residue field of the local algebraic
  closure (`localInertiaGroup` is the inertia subgroup of the maximal
  ideal of the integral closure), and reduction is Galois-equivariant,
  so `red (σ P) = red P` for `σ` inertial;
* hits every `p`-torsion point of `Ẽ`: reduction is surjective on
  points over the local algebraic closure (Hensel's lemma, the residue
  field being algebraically closed), and the kernel of reduction — the
  points of the formal group over the valuation ring of the local
  algebraic closure — is `p`-divisible there, so a `p`-torsion point of
  `Ẽ` lifts first to a point of `E` and then, after correcting by a
  `p`-th root inside the kernel of reduction, to a `p`-torsion point.

The kernel of `red` on the `p`-torsion is exactly the connected
(formal-group) part of the connected-étale sequence of `E[p]/ℤ_p`.
Silverman AEC VII.2 (reduction and its kernel), VII.3.1, IV.2–IV.3
(formal groups, `p`-divisibility); Silverman ATAEC IV.6; the
kernel-of-reduction lemmas of `Flat.lean`
(`kernel_add_abscissa_notMem`,
`kernel_sub_abscissa_notMem_of_residue_eq`) are the intended supply
line for the valuation-theoretic half.

ROUTE TAKEN (2026-07-25). The surjectivity clause — the only one with
content, the inertia clause being inherited verbatim from the map on
all points — is proved by LIFT AND CORRECT, which is what splits this
node into its two bricks. Given `y ∈ Ẽ(𝔽̄_p)[p]`, surjectivity of
reduction on ALL points (Hensel, brick one) gives some `P ∈ E(ℚ̄_p)`
with `red P = y`; then `red (p • P) = p • y = 0`, so `p • P` lies in
the kernel of reduction `E₁ = Ê(𝔪)`, and `p`-divisibility of that
kernel (Newton polygon over `𝒪_{ℚ̄_p}`, brick two) gives `Z ∈ E₁` with
`p • Z = p • P`. Then `P − Z` is `p`-torsion and still reduces to `y`.

Why the correction step cannot be avoided, and why the two bricks are
genuinely independent: the naive attempt to prove brick two by choosing
`Q` with `p • Q = P` and then correcting `Q` by a `p`-torsion point is
CIRCULAR — it needs exactly the surjectivity of `red` on `E[p]` that is
being proved here. Brick two must therefore be proved analytically, over
the completion `ℂ_p` (where the formal group is over a complete ring, so
Weierstrass preparation applies), and pulled back to `ℚ̄_p` by the
observation that the solutions are algebraic over `ℚ_p`.

An alternative route to the same node, recorded but NOT taken: since the
source has exactly `p²` elements (`TorsionCard.card_torsionBy`, as used
in `not_local_inertia_eigenvector_of_good_of_supersingular`) and the
target `Ẽ(𝔽̄_p)[p]` has order dividing `p`
(`card_torsionBy_dvd_of_charP`), surjectivity of `red` onto `Ẽ(𝔽̄_p)[p]`
is EQUIVALENT to the kernel of `red` on `E[p]` having order
`p² / #Ẽ(𝔽̄_p)[p]`, i.e. to the exactness of the connected-étale
sequence; that counting route would replace both bricks by one
order computation. -/
theorem WeierstrassCurve.exists_localReductionHom_of_good_reduction
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : p.Prime)
    [E.HasGoodReduction
      (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)] :
    ∃ red : AddSubgroup.torsionBy
        ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
          (HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat))).Point ((p : ℕ) : ℤ) →+
        ((E.reduction
          (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal))⁄
          (AlgebraicClosure (IsLocalRing.ResidueField
            (Localization.AtPrime
              hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)))).Point,
      (∀ σ ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat,
        ∀ (P Q : AddSubgroup.torsionBy
          ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
            (HeightOneSpectrum.adicCompletion ℚ
              hp.toHeightOneSpectrumRingOfIntegersRat))).Point ((p : ℕ) : ℤ)),
          (Q : ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
            (HeightOneSpectrum.adicCompletion ℚ
              hp.toHeightOneSpectrumRingOfIntegersRat))).Point) =
            WeierstrassCurve.Affine.Point.map
              (W' := E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat)))
              ((σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                  hp.toHeightOneSpectrumRingOfIntegersRat))
                ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
                  hp.toHeightOneSpectrumRingOfIntegersRat]
                (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                  hp.toHeightOneSpectrumRingOfIntegersRat)))).toAlgHom
              (P : ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
                (HeightOneSpectrum.adicCompletion ℚ
                  hp.toHeightOneSpectrumRingOfIntegersRat))).Point) →
          red Q = red P) ∧
      ∀ y ∈ AddSubgroup.torsionBy
          ((E.reduction
            (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal))⁄
            (AlgebraicClosure (IsLocalRing.ResidueField
              (Localization.AtPrime
                hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)))).Point
          ((p : ℕ) : ℤ),
        ∃ P, red P = y := by
  classical
  obtain ⟨red₀, hsurj, hinv, hker⟩ :=
    E.exists_localReductionAddHom_of_good_reduction hp
  -- The kernel of `red₀` is `p`-divisible: by `hker` it is exactly the
  -- non-integral locus, on which the formal-group leaf
  -- `exists_localKernelDivision_of_good_reduction` produces a `p`-th part
  -- inside the same locus.
  have hkerdiv : ∀ P : ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
      (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat))).Point,
      red₀ P = 0 → ∃ Z, red₀ Z = 0 ∧ ((p : ℕ) : ℤ) • Z = P := by
    rintro (_ | ⟨x, y, h⟩) hP
    · exact ⟨0, map_zero red₀, zsmul_zero _⟩
    · obtain ⟨x', y', h', hx', heq⟩ :=
        E.exists_localKernelDivision_of_good_reduction hp x y h ((hker x y h).mp hP)
      exact ⟨WeierstrassCurve.Affine.Point.some x' y' h',
        (hker x' y' h').mpr hx', heq⟩
  refine ⟨red₀.comp (AddSubgroup.subtype _), ?_, ?_⟩
  · -- inertia invariance is inherited from `red₀` unchanged
    intro σ hσ P Q hQ
    show red₀ (Q : ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat))).Point) =
      red₀ (P : ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat))).Point)
    rw [hQ]
    exact hinv σ hσ _
  · -- surjectivity onto the `p`-torsion: lift along `hsurj`, then correct the
    -- lift by a `p`-th part of `p • P` taken inside the kernel
    intro y hy
    obtain ⟨P, hP⟩ := hsurj y
    have hpy : ((p : ℕ) : ℤ) • y = 0 := (Submodule.mem_torsionBy_iff _ _).mp hy
    have h0 : red₀ (((p : ℕ) : ℤ) • P) = 0 := by
      rw [map_zsmul, hP, hpy]
    obtain ⟨Z, hZ0, hZ⟩ := hkerdiv _ h0
    have hmem : ((p : ℕ) : ℤ) • (P - Z) = 0 := by
      rw [zsmul_sub, hZ, sub_self]
    have hval : red₀ (P - Z) = y := by
      rw [map_sub, hP, hZ0, sub_zero]
    exact ⟨⟨P - Z, (Submodule.mem_torsionBy_iff _ _).mpr hmem⟩, hval⟩

/-- **The residue characteristic of the `p`-place of `ℚ` is `p`** (PROVEN
2026-07-25): `p` lies in the height-one prime `v_p ⊆ 𝓞 ℚ`
(`mem_toHeightOneSpectrumRingOfIntegersRat_asIdeal`), hence its image in
the localization `ℤ_(p)` lies in the maximal ideal
(`Localization.AtPrime.map_eq_maximalIdeal`), hence dies in the residue
field. Consumed by `card_torsion_reduction_of_good_ordinary` to feed the
characteristic hypothesis of the char-`p` torsion bound. -/
theorem residue_natCast_eq_zero_of_prime {p : ℕ} (hp : p.Prime) :
    ((p : ℕ) : IsLocalRing.ResidueField
      (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)) = 0 := by
  have hmemP : ((p : ℕ) : NumberField.RingOfIntegers ℚ) ∈
      hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal := by
    rw [hp.mem_toHeightOneSpectrumRingOfIntegersRat_asIdeal, map_natCast]
  have hmem : (algebraMap (NumberField.RingOfIntegers ℚ)
      (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal))
      ((p : ℕ) : NumberField.RingOfIntegers ℚ) ∈
      IsLocalRing.maximalIdeal
        (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ hmemP
  rw [map_natCast] at hmem
  exact (IsLocalRing.residue_eq_zero_iff _).mpr hmem

open scoped WeierstrassCurve.Affine in
/-- **In characteristic `p`, the geometric `p`-torsion of an elliptic
curve is cyclic** (PROVEN 2026-07-25 from
`TorsionCharP.exists_zsmul_eq_of_charP`; cut 2026-07-25 out of
`card_torsionBy_dvd_of_charP` — this is ALL of that leaf's mathematical
content, the cardinality bookkeeping around it now being proven): over an
algebraically closed field `k` in which `p` vanishes, every `p`-torsion
point of `Y` is a `ℤ`-multiple of every NONZERO `p`-torsion point. Since
the group is killed by `p`, that is exactly `dim_{𝔽ₚ} Y(k)[p] ≤ 1`, and
`card_torsionBy_dvd_of_charP` follows from it by taking a generator.

FAITHFULNESS CHECK: both cases of the classical dichotomy satisfy this.
Ordinary, `Y(k)[p] ≅ ℤ/p`: any nonzero point generates. Supersingular,
`Y(k)[p] = 0`: the hypothesis `Q ≠ 0` is unsatisfiable. Note that the
statement is NOT vacuous — in the ordinary case it has real content, and
it is exactly what fails for `p` invertible in `k`, where the torsion is
`(ℤ/p)²` and two independent points exist.

CONTENT. In characteristic `p` the multiplication-by-`p` isogeny has
degree `p²` but is never separable — it acts as multiplication by
`p = 0` on invariant differentials — so its separable degree, which is
the number of geometric points of its kernel, is `p` or `1`. Silverman
AEC III.6.4 (the differential criterion for separability), III.4.10
(separable degree = number of geometric points of the kernel), V.3.1
(a)–(b) (the ordinary/supersingular dichotomy); ATAEC IV.6.

HOW IT WAS CLOSED (2026-07-25). Mathlib indeed has no isogenies, no
separable/inseparable degree, no Frobenius on a Weierstrass curve and no
invariant differential — but this repository already had every input, in
`Fermat/FLT/EllipticCurve/`, built for the COMPLEMENTARY case
`(p : k) ≠ 0` (`TorsionCard.prime_torsion_card`, `#E[p] = p²`). The
earlier survey in this docstring, which declared all three sub-atoms
missing, was a survey of MATHLIB only; the three needed statements were
already proven here. So the char-`p` case is a short argument, collected
in `Fermat/FLT/EllipticCurve/TorsionCharP.lean`:

* BRIDGE — `TorsionCard.smul_some_eq_zero_iff` (already proven): for a
  point `(x, y)` and `n ≠ 0`, `n • P = 0 ↔ (ΨSqₙ).eval x = 0`.
* NONVANISHING — `TorsionCharP.ΨSq_ne_zero`: needs no characteristic
  hypothesis at all. `IsCoprime a 0` forces `a` to be a unit, so
  coprimality of `Φₙ` and `ΨSqₙ` (`WeierstrassCurve.isCoprime_Φ_ΨSq`,
  proven from `Δ ≠ 0`) together with `natDegree_Φ n = n² > 0` already
  gives `ΨSqₙ ≠ 0`. The leading-coefficient route, which does fail here
  because `coeff_ΨSq n = n²` vanishes, is simply not needed.
* INSEPARABILITY — `TorsionCharP.derivative_ΨSq_eq_zero_of_charP`: the
  differential criterion `[p]* ω = p ⬝ ω = 0` is available in polynomial
  form as the Wronskian identity
  `Φₙ′ ⬝ ΨSqₙ − Φₙ ⬝ ΨSqₙ′ = n ⬝ preΨ₂ₙ` (`PsiSumCompanion.wronskian`,
  proven at the tautological point of the universal curve). At `n = p`
  in characteristic `p` the right-hand side vanishes, so
  `ΨSqₚ ∣ Φₚ ⬝ ΨSqₚ′`; coprimality upgrades this to `ΨSqₚ ∣ ΨSqₚ′`, and
  a nonzero polynomial cannot divide its own derivative unless that
  derivative is `0`. Over the perfect field `k` this makes `ΨSqₚ` a
  `p`-th power (`TorsionCharP.exists_pow_eq_ΨSq_of_charP`), so it has at
  most `(p² − 1)/p ≤ p − 1` DISTINCT roots.

The count then runs on the FULL group rather than on `x`-coordinate
pairs: if `P` were not a multiple of `Q`, the `p²` points `a • Q + b • P`
(`0 ≤ a, b < p`) would be pairwise distinct (Bézout for `p` turns any
coincidence into `P ∈ ℤ ⬝ Q`), giving `p² − 1` nonzero `p`-torsion
points; each `x`-coordinate is one of at most `p − 1` roots and carries
at most two points (`TorsionCard.pointsAt_card`), so
`p² − 1 ≤ 2(p − 1)`, i.e. `(p − 1)² ≤ 0`. This works uniformly for
`p = 2` as well, so no separate even case is needed.

SANITY CHECK in characteristic `2`, which validates the shape of
INSEPARABILITY: `ΨSq 2 = Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆` collapses to
`b₂X² + b₆ = a₁²X² + a₃² = (a₁X + a₃)²`, a perfect square exactly as
predicted. It is a nonzero constant precisely when `a₁ = 0`, which in
characteristic `2` is precisely the supersingular case, and then
`a₃ ≠ 0` because `Δ ≠ 0`. Both predictions hold. -/
theorem WeierstrassCurve.exists_zsmul_eq_of_mem_torsionBy_of_charP
    {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k]
    (Y : WeierstrassCurve k) [Y.IsElliptic]
    {p : ℕ} (hp : p.Prime) (hchar : ((p : ℕ) : k) = 0)
    (P Q : (Y⁄k).Point)
    (hP : P ∈ AddSubgroup.torsionBy (Y⁄k).Point ((p : ℕ) : ℤ))
    (hQ : Q ∈ AddSubgroup.torsionBy (Y⁄k).Point ((p : ℕ) : ℤ)) (hQ0 : Q ≠ 0) :
    ∃ n : ℤ, P = n • Q :=
  TorsionCharP.exists_zsmul_eq_of_charP Y hp hchar P Q
    ((Submodule.mem_torsionBy_iff _ _).mp hP) ((Submodule.mem_torsionBy_iff _ _).mp hQ) hQ0

open scoped WeierstrassCurve.Affine in
/-- **The geometric `p`-torsion of an elliptic curve in characteristic
`p` has order dividing `p`** (DERIVED 2026-07-25 from the cyclicity atom
`exists_zsmul_eq_of_mem_torsionBy_of_charP`, which now carries all of the
mathematical content; itself cut 2026-07-25 out of
`card_torsion_reduction_of_good_ordinary` — ALL of that leaf's
characteristic-`p` content, now stated free of every local-field and
Frey-curve encumbrance): for an elliptic curve `Y` over an algebraically
closed field `k` of characteristic `p`, `#Y(k)[p]` divides `p`.

Content: in characteristic `p` the multiplication-by-`p` isogeny of an
elliptic curve has degree `p²` but is never separable — its induced map
on the space of invariant differentials is multiplication by `p = 0` — so
it factors as `Frobenius ∘ (something)` and its inseparable degree is `p`
or `p²`. Hence the number of GEOMETRIC points of its kernel, which is the
separable degree, is `p` (ordinary case) or `1` (supersingular case); in
both cases a divisor of `p`. Silverman AEC III.6.4 (the differential
criterion for separability), V.3.1 (a)–(b) (the ordinary/supersingular
dichotomy), III.4.10 (separable degree = number of geometric points of
the kernel); Silverman ATAEC IV.6.

Note the hypothesis is only that `p` vanishes in `k` — `p` need not be
the characteristic exponent in any stronger sense, and `k` is only
required to be algebraically closed, so this statement is a candidate for
mathlib once the isogeny-degree machinery exists there.

The derivation from cyclicity is the whole proof below: a generator of
the torsion subgroup exists (take `0` when the subgroup is trivial, and
any nonzero element otherwise, the atom promoting it to a generator), so
the subgroup coincides with the `zmultiples` of that generator, whence
its cardinality is the additive order of the generator, which divides `p`
because the subgroup is `p`-torsion. No finiteness input is needed: being
generated by an element of order dividing `p` supplies it. -/
theorem WeierstrassCurve.card_torsionBy_dvd_of_charP
    {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k]
    (Y : WeierstrassCurve k) [Y.IsElliptic]
    {p : ℕ} (hp : p.Prime) (hchar : ((p : ℕ) : k) = 0) :
    Nat.card (AddSubgroup.torsionBy (Y⁄k).Point ((p : ℕ) : ℤ)) ∣ p := by
  -- a generator of the `p`-torsion, uniformly in the trivial and nontrivial cases
  have hgen : ∃ Q ∈ AddSubgroup.torsionBy (Y⁄k).Point ((p : ℕ) : ℤ),
      ∀ P ∈ AddSubgroup.torsionBy (Y⁄k).Point ((p : ℕ) : ℤ), ∃ n : ℤ, P = n • Q := by
    by_cases hex : ∃ Q ∈ AddSubgroup.torsionBy (Y⁄k).Point ((p : ℕ) : ℤ), Q ≠ 0
    · obtain ⟨Q, hQT, hQ0⟩ := hex
      exact ⟨Q, hQT, fun P hP =>
        WeierstrassCurve.exists_zsmul_eq_of_mem_torsionBy_of_charP Y hp hchar P Q hP hQT hQ0⟩
    · refine ⟨0, zero_mem _, fun P hP => ⟨0, ?_⟩⟩
      have hP0 : P = 0 := by by_contra h; exact hex ⟨P, hP, h⟩
      simp [hP0]
  obtain ⟨Q, hQT, hQgen⟩ := hgen
  set T := AddSubgroup.torsionBy (Y⁄k).Point ((p : ℕ) : ℤ)
  set q : T := ⟨Q, hQT⟩
  -- the generator generates, so the subgroup is its group of multiples
  have htop : AddSubgroup.zmultiples q = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨n, hn⟩ := hQgen (x : (Y⁄k).Point) x.2
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, Subtype.ext (by simpa using hn.symm)⟩
  have hcard : Nat.card T = addOrderOf q := by
    rw [← Nat.card_zmultiples q, htop, AddSubgroup.card_top]
  rw [hcard]
  exact addOrderOf_dvd_of_nsmul_eq_zero (AddSubgroup.torsionBy.nsmul q)

open ValuativeRel IsDedekindDomain in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
/-- **Ordinary reduction: the geometric `p`-torsion of the reduced curve
has order exactly `p`** (DERIVED 2026-07-25 from the char-`p` bound
`card_torsionBy_dvd_of_charP` and the residue-characteristic computation
`residue_natCast_eq_zero_of_prime`; previously a sorry node, cut out of
`exists_localTorsionQuotient_of_good_ordinary` — the second brick of the
ordinary case, and the one carrying the *characteristic-`p`* content):
if the reduction `Ẽ` of a curve with good reduction at `p` has a nonzero
geometric `p`-torsion point (this is the definition of ordinarity used
here), then `Ẽ(𝔽̄_p)[p]` has exactly `p` elements.

In characteristic `p` the multiplication-by-`p` isogeny of an elliptic
curve has degree `p²` and inseparable degree `p` or `p²`; hence its
kernel of geometric points is either cyclic of order `p` (ordinary) or
trivial (supersingular). Ordinarity excludes the second case, and the
first is exactly the claim. Silverman AEC V.3.1 (a)–(b) and III.6.4;
Silverman ATAEC IV.6. -/
theorem WeierstrassCurve.card_torsion_reduction_of_good_ordinary
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : p.Prime)
    [E.HasGoodReduction
      (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)]
    (hord : ∃ P : ((E.reduction
        (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal))⁄
        (AlgebraicClosure (IsLocalRing.ResidueField
          (Localization.AtPrime
            hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)))).Point,
      P ≠ 0 ∧ (p : ℤ) • P = 0) :
    Nat.card (AddSubgroup.torsionBy
      ((E.reduction
        (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal))⁄
        (AlgebraicClosure (IsLocalRing.ResidueField
          (Localization.AtPrime
            hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)))).Point
      ((p : ℕ) : ℤ)) = p := by
  classical
  -- the reduced curve is elliptic, by the definition of good reduction
  haveI : (E.reduction
      (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)).IsElliptic :=
    (WeierstrassCurve.hasGoodReduction_iff_isElliptic_reduction
      (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)).mp
      inferInstance
  -- the residue characteristic is `p`, and so is the characteristic of its closure
  have hchar : ((p : ℕ) : AlgebraicClosure (IsLocalRing.ResidueField
      (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal))) = 0 := by
    rw [← map_natCast (algebraMap (IsLocalRing.ResidueField
      (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal))
      (AlgebraicClosure (IsLocalRing.ResidueField
        (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)))) p,
      residue_natCast_eq_zero_of_prime hp, map_zero]
  -- the char-`p` bound: the geometric `p`-torsion has order dividing `p`
  have hdvd := WeierstrassCurve.card_torsionBy_dvd_of_charP
    ((E.reduction
      (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)).map
      (algebraMap (IsLocalRing.ResidueField
        (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal))
        (AlgebraicClosure (IsLocalRing.ResidueField
          (Localization.AtPrime
            hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal))))) hp hchar
  -- ordinarity rules out the trivial case, so the order is exactly `p`
  obtain ⟨P, hP0, hPtor⟩ := hord
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp _ hdvd) with h1 | hpp
  · exfalso
    obtain ⟨hsub, -⟩ := Nat.card_eq_one_iff_unique.mp h1
    exact hP0 (congrArg Subtype.val
      (hsub.allEq (⟨P, (Submodule.mem_torsionBy_iff _ _).mpr hPtor⟩) 0))
  · exact hpp

open ValuativeRel IsDedekindDomain in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
/-- **The local connected-étale torsion quotient at a good ORDINARY
prime** (PROVEN — the surviving local content of the ordinary
case, cut 2026-07-23 at the same seam as the PROVEN multiplicative
quotients `exists_localTorsionQuotient_of_split` /
`_of_nonsplit`): for an elliptic curve over `ℚ` with good ordinary
reduction at an odd prime `p` (ordinarity stated as the existence of a
nonzero geometric `p`-torsion point of the reduced curve `Ẽ/𝔽_p`), the
`p`-torsion of the completed base change over the local algebraic
closure surjects onto `ℤ/p` invariantly under the local INERTIA: the
étale quotient of the connected-étale sequence of the finite flat
group scheme `E[p]/ℤ_p` has order `p` by ordinarity, and its geometric
points are constant over the maximal unramified extension. The kernel
is the connected (formal-group) line. Serre Duke 1987, §4.1; Silverman
ATAEC IV.6, V; the finite-flat infrastructure of `Flat.lean`
(`torsion_flat_of_good_reduction`, the kernel-of-reduction lemmas) is
the intended supply line. -/
theorem WeierstrassCurve.exists_localTorsionQuotient_of_good_ordinary
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : p.Prime) (_hodd : p ≠ 2)
    [E.HasGoodReduction
      (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)]
    (hord : ∃ P : ((E.reduction
        (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal))⁄
        (AlgebraicClosure (IsLocalRing.ResidueField
          (Localization.AtPrime
            hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)))).Point,
      P ≠ 0 ∧ (p : ℤ) • P = 0) :
    ∃ π : AddSubgroup.torsionBy
        ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
          (HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat))).Point ((p : ℕ) : ℤ) →+
        ZMod p,
      Function.Surjective π ∧
      ∀ σ ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat,
        ∀ (P Q : AddSubgroup.torsionBy
          ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
            (HeightOneSpectrum.adicCompletion ℚ
              hp.toHeightOneSpectrumRingOfIntegersRat))).Point ((p : ℕ) : ℤ)),
          (Q : ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
            (HeightOneSpectrum.adicCompletion ℚ
              hp.toHeightOneSpectrumRingOfIntegersRat))).Point) =
            WeierstrassCurve.Affine.Point.map
              (W' := E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat)))
              ((σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                  hp.toHeightOneSpectrumRingOfIntegersRat))
                ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
                  hp.toHeightOneSpectrumRingOfIntegersRat]
                (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                  hp.toHeightOneSpectrumRingOfIntegersRat)))).toAlgHom
              (P : ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
                (HeightOneSpectrum.adicCompletion ℚ
                  hp.toHeightOneSpectrumRingOfIntegersRat))).Point) →
          π Q = π P := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  -- the two bricks: the reduction homomorphism, and the order of `Ẽ(𝔽̄_p)[p]`
  obtain ⟨red, hredinv, hredsurj⟩ :=
    E.exists_localReductionHom_of_good_reduction hp
  have hcard := E.card_torsion_reduction_of_good_ordinary hp hord
  -- a group of prime order is cyclic, hence isomorphic to `ℤ/p`
  have hcyc := isAddCyclic_of_prime_card hcard
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have e := zmodAddEquivOfGenerator hg hcard
  -- `red` lands in the `p`-torsion of the reduced curve: it is a homomorphism out of a
  -- group killed by `p`
  have hmem : ∀ P, red P ∈ AddSubgroup.torsionBy
      ((E.reduction
        (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal))⁄
        (AlgebraicClosure (IsLocalRing.ResidueField
          (Localization.AtPrime
            hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)))).Point
      ((p : ℕ) : ℤ) := by
    intro P
    refine AddSubgroup.torsionBy.nsmul_iff.mpr ?_
    calc (p : ℕ) • red P = red ((p : ℕ) • P) := (map_nsmul red p P).symm
      _ = red 0 := by rw [AddSubgroup.torsionBy.nsmul P]
      _ = 0 := map_zero red
  refine ⟨e.symm.toAddMonoidHom.comp (red.codRestrict _ hmem), ?_, ?_⟩
  · -- surjectivity: every element of `ℤ/p` is `e.symm` of a value of `red`
    intro c
    obtain ⟨P, hP⟩ := hredsurj _ (e c).2
    refine ⟨P, ?_⟩
    have hPT : (red.codRestrict _ hmem) P = e c := Subtype.ext hP
    show e.symm ((red.codRestrict _ hmem) P) = c
    rw [hPT, AddEquiv.symm_apply_apply]
  · -- inertia invariance: inherited from the invariance of `red`
    intro σ hσ P Q hQ
    have h1 : red Q = red P := hredinv σ hσ P Q hQ
    have h2 : (red.codRestrict _ hmem) Q = (red.codRestrict _ hmem) P := Subtype.ext h1
    show e.symm ((red.codRestrict _ hmem) Q) = e.symm ((red.codRestrict _ hmem) P)
    rw [h2]

open IsDedekindDomain in
set_option backward.isDefEq.respectTransparency false in
/-- **The connected-étale line at a good ORDINARY prime** (DERIVED
2026-07-23 from the local quotient leaf
`exists_localTorsionQuotient_of_good_ordinary` and the PROVEN
reduction-agnostic `ℚ̄`-pullback glue
`exists_etale_line_of_localTorsionQuotient`): for an elliptic curve
over `ℚ` with good ordinary reduction at an odd prime `p` there is a
line `L ⊆ E[p]` (the connected line of the connected-étale sequence)
such that inertia at `p` acts trivially on `E[p]/L`. Serre Duke 1987,
§4.1; Silverman ATAEC V. -/
theorem WeierstrassCurve.exists_etale_line_of_good_of_ordinary
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    [E.HasGoodReduction
      (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)]
    (hord : ∃ P : ((E.reduction
        (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal))⁄
        (AlgebraicClosure (IsLocalRing.ResidueField
          (Localization.AtPrime
            hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)))).Point,
      P ≠ 0 ∧ (p : ℤ) • P = 0) :
    ∃ L : Submodule (ZMod p) ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p),
      Module.finrank (ZMod p) L = 1 ∧
      ∀ σ ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat,
        ∀ v, L.mkQ (E.galoisRep p hp.pos
            ((Field.absoluteGaloisGroup.map (algebraMap ℚ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat))) σ) v) = L.mkQ v := by
  obtain ⟨π, hπsurj, hπinv⟩ :=
    E.exists_localTorsionQuotient_of_good_ordinary hp hodd hord
  exact E.exists_etale_line_of_localTorsionQuotient hp π hπsurj hπinv

/-- **The Borel exponent bound, pure group theory** (PROVEN 2026-07-25 —
the linear-algebra brick of the supersingular case, extracted as a
statement about an abstract group so that it can be verified without the
elliptic-curve plumbing): let `A` be an abelian group of exponent `p` and
order `p²` — i.e. a `2`-dimensional `𝔽_p`-vector space — and let `f` be an
injective endomorphism of `A` admitting an eigenvector `Q ≠ 0`, say
`f Q = c • Q`. Then `f ^ (p (p − 1))` is the identity.

Proof, in matrix language: in a basis `(Q, w)` the matrix of `f` is upper
triangular, `[[c, *], [0, d]]` with `c, d ∈ 𝔽_pˣ`; Fermat's little theorem
makes `τ = f ^ (p − 1)` unipotent, and a unipotent matrix in characteristic
`p` satisfies `τ ^ p = 1`. The proof below avoids choosing `w`: the
eigenline `L = ⟨Q⟩` is `f`-stable and has index `p`, so the quotient `A/L`
is cyclic of order `p` and `f` acts on it as multiplication by some `d`
prime to `p` (else `f` would not be injective). Fermat gives
`τ Q = Q` and `τ x ≡ x mod L`, whence `τ` fixes `L` pointwise and
`τ ^ n x = x + n • (τ x − x)`; taking `n = p` and using the exponent kills
the correction term. -/
theorem borel_bound_iterate_eq_self
    {A : Type*} [AddCommGroup A] {p : ℕ} (hp : p.Prime)
    (f : A →+ A) (hinj : Function.Injective f)
    (hexp : ∀ a : A, (p : ℕ) • a = 0)
    (hcard : Nat.card A = p ^ 2)
    {Q : A} (hQ0 : Q ≠ 0) {c : ℤ} (hfQ : f Q = c • Q)
    (a : A) : (f : A → A)^[p * (p - 1)] a = a := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hfin : Finite A := Nat.finite_of_card_ne_zero (by
    rw [hcard]; exact pow_ne_zero 2 hp.ne_zero)
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
  -- the eigenline
  have hQord : addOrderOf Q = p := addOrderOf_eq_prime (hexp Q) hQ0
  have hcardL : Nat.card (AddSubgroup.zmultiples Q) = p := by
    rw [Nat.card_zmultiples, hQord]
  have hfL : AddSubgroup.zmultiples Q ≤ (AddSubgroup.zmultiples Q).comap f := by
    intro x hx
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    refine AddSubgroup.mem_comap.mpr ?_
    rw [← hk, map_zsmul, hfQ, smul_smul]
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨k * c, rfl⟩
  -- the quotient by the eigenline has order `p`
  have hcardB : Nat.card (A ⧸ AddSubgroup.zmultiples Q) = p := by
    have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
      (AddSubgroup.zmultiples Q)
    rw [hcard, hcardL, pow_two] at h1
    exact (Nat.eq_of_mul_eq_mul_right hp.pos h1).symm
  set fb : AddMonoid.End (A ⧸ AddSubgroup.zmultiples Q) :=
    QuotientAddGroup.map _ _ f hfL with hfbdef
  have hmkf : ∀ x : A, fb (QuotientAddGroup.mk' _ x) = QuotientAddGroup.mk' _ (f x) :=
    fun x => QuotientAddGroup.map_mk' _ _ f hfL x
  -- composition of endomorphisms is application
  have hmulappA : ∀ (G H : AddMonoid.End A) (x : A), (G * H) x = G (H x) :=
    fun _ _ _ => rfl
  have hmulappB : ∀ (G H : AddMonoid.End (A ⧸ AddSubgroup.zmultiples Q))
      (x : A ⧸ AddSubgroup.zmultiples Q), (G * H) x = G (H x) := fun _ _ _ => rfl
  -- the induced map on the quotient is multiplication by a scalar `d`
  obtain ⟨g, hg⟩ := (isAddCyclic_of_prime_card hcardB).exists_generator
  obtain ⟨d, hd⟩ := AddSubgroup.mem_zmultiples_iff.mp (hg (fb g))
  have hfbx : ∀ x : A ⧸ AddSubgroup.zmultiples Q, fb x = d • x := by
    intro x
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (hg x)
    rw [← hk, map_zsmul, ← hd, smul_comm]
  have hexpB : ∀ x : A ⧸ AddSubgroup.zmultiples Q, (p : ℕ) • x = 0 := by
    intro x
    obtain ⟨a', rfl⟩ := QuotientAddGroup.mk'_surjective _ x
    rw [← map_nsmul, hexp a', map_zero]
  -- `d` is invertible mod `p`, else `f` would not be injective
  have hdne : ¬ ((p : ℤ) ∣ d) := by
    intro ⟨m, hm⟩
    have hzero : ∀ x : A ⧸ AddSubgroup.zmultiples Q, x = 0 := by
      intro x
      obtain ⟨y, rfl⟩ : ∃ y, fb y = x := by
        obtain ⟨a', rfl⟩ := QuotientAddGroup.mk'_surjective _ x
        obtain ⟨b, hb⟩ := hsurj a'
        exact ⟨QuotientAddGroup.mk' _ b, by rw [hmkf, hb]⟩
      rw [hfbx, hm, mul_smul, natCast_zsmul, hexpB]
    have hone : Nat.card (A ⧸ AddSubgroup.zmultiples Q) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun x y => by rw [hzero x, hzero y]⟩, ⟨0⟩⟩
    rw [hcardB] at hone
    exact hp.one_lt.ne' hone
  -- `c` is invertible mod `p`, for the same reason
  have hcne : ¬ ((p : ℤ) ∣ c) := by
    intro ⟨m, hm⟩
    apply hQ0
    apply hinj
    rw [hfQ, hm, mul_smul, natCast_zsmul, hexp, map_zero]
  -- Fermat's little theorem, in the divisibility form used twice below
  have hfermat : ∀ e : ℤ, ¬ ((p : ℤ) ∣ e) → (p : ℤ) ∣ e ^ (p - 1) - 1 := by
    intro e he
    have h1 : ((e : ZMod p)) ≠ 0 := fun h =>
      he ((ZMod.intCast_zmod_eq_zero_iff_dvd e p).mp h)
    have h2 : ((e : ZMod p)) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h1
    have h3 : ((e ^ (p - 1) - 1 : ℤ) : ZMod p) = 0 := by push_cast; rw [h2, sub_self]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h3
  have hkillA : ∀ (e : ℤ) (x : A), (p : ℤ) ∣ e - 1 → e • x = x := by
    intro e x hdvd
    obtain ⟨m, hm⟩ := hdvd
    have he : e = 1 + (p : ℤ) * m := by omega
    rw [he, add_smul, one_smul, mul_smul, natCast_zsmul, hexp, add_zero]
  have hkillB : ∀ (e : ℤ) (x : A ⧸ AddSubgroup.zmultiples Q),
      (p : ℤ) ∣ e - 1 → e • x = x := by
    intro e x hdvd
    obtain ⟨m, hm⟩ := hdvd
    have he : e = 1 + (p : ℤ) * m := by omega
    rw [he, add_smul, one_smul, mul_smul, natCast_zsmul, hexpB, add_zero]
  -- `τ = f ^ (p - 1)`
  set F : AddMonoid.End A := f with hFdef
  -- the two facts about `f`, restated with the `AddMonoid.End` coercion
  have hfQF : F Q = c • Q := hfQ
  have hmkfF : ∀ x : A,
      fb (QuotientAddGroup.mk' (AddSubgroup.zmultiples Q) x) =
        QuotientAddGroup.mk' (AddSubgroup.zmultiples Q) (F x) := hmkf
  have hFQ : ∀ n : ℕ, (F ^ n) Q = (c ^ n) • Q := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', hmulappA, ih, map_zsmul, hfQF, smul_smul, pow_succ]
  have hτQ : (F ^ (p - 1)) Q = Q := by
    rw [hFQ]
    exact hkillA _ _ (hfermat c hcne)
  -- `τ` fixes the eigenline pointwise
  have hτL : ∀ x ∈ AddSubgroup.zmultiples Q, (F ^ (p - 1)) x = x := by
    intro x hx
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    rw [← hk, map_zsmul, hτQ]
  -- `τ` is the identity on the quotient
  have hmkF : ∀ (n : ℕ) (x : A),
      QuotientAddGroup.mk' (AddSubgroup.zmultiples Q) ((F ^ n) x) =
        (fb ^ n) (QuotientAddGroup.mk' (AddSubgroup.zmultiples Q) x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ', hmulappA, ← hmkfF, ih, pow_succ', hmulappB]
  have hfbn : ∀ (n : ℕ) (x : A ⧸ AddSubgroup.zmultiples Q),
      (fb ^ n) x = (d ^ n) • x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ', hmulappB, ih, map_zsmul, hfbx, smul_smul, pow_succ]
  have hτquot : ∀ x : A, (F ^ (p - 1)) x - x ∈ AddSubgroup.zmultiples Q := by
    intro x
    rw [← QuotientAddGroup.eq_zero_iff]
    have h1 : QuotientAddGroup.mk' (AddSubgroup.zmultiples Q) ((F ^ (p - 1)) x) =
        QuotientAddGroup.mk' (AddSubgroup.zmultiples Q) x := by
      rw [hmkF, hfbn]
      exact hkillB _ _ (hfermat d hdne)
    have h2 : QuotientAddGroup.mk' (AddSubgroup.zmultiples Q)
        ((F ^ (p - 1)) x - x) = 0 := by rw [map_sub, h1, sub_self]
    exact h2
  -- the unipotence induction `τ ^ n x = x + n • (τ x - x)`
  have hunip : ∀ (n : ℕ) (x : A),
      ((F ^ (p - 1)) ^ n) x = x + n • ((F ^ (p - 1)) x - x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ', hmulappA, ih, map_add, map_nsmul, hτL _ (hτquot x), succ_nsmul]
      abel
  have hpow : F ^ (p * (p - 1)) = (F ^ (p - 1)) ^ p := by
    rw [mul_comm, pow_mul]
  have hfinal : (F ^ (p * (p - 1))) a = a := by
    rw [hpow, hunip, hexp, add_zero]
  exact hfinal

open scoped WeierstrassCurve.Affine in
/-- **Iterating a Galois automorphism on points** (PROVEN 2026-07-25):
the action of `σ ^ n` on the points of a Weierstrass curve over a field
extension is the `n`-fold iterate of the action of `σ`, since
`Point.map` is functorial (`Point.map_map`) and the monoid structure on
`L ≃ₐ[K] L` is composition. -/
theorem WeierstrassCurve.point_map_algEquiv_pow
    {K : Type*} [Field K] (X : WeierstrassCurve K)
    {L : Type*} [Field L] [Algebra K L] [DecidableEq L]
    (σ : L ≃ₐ[K] L) (n : ℕ) (P : (X⁄L).Point) :
    WeierstrassCurve.Affine.Point.map (W' := X) ((σ ^ n : L ≃ₐ[K] L)).toAlgHom P =
      (fun R => WeierstrassCurve.Affine.Point.map (W' := X) σ.toAlgHom R)^[n] P := by
  induction n generalizing P with
  | zero => cases P <;> rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ← ih, pow_succ]
    rw [WeierstrassCurve.Affine.Point.map_map]
    rfl

open scoped WeierstrassCurve.Affine in
/-- **The Borel bound on the `p`-torsion of a curve** (PROVEN 2026-07-25
from `borel_bound_iterate_eq_self` and `point_map_algEquiv_pow`): if a
nonzero `p`-torsion point `Q` of `X` over a field extension `L/K` is an
eigenvector of `σ ∈ Aut(L/K)`, and the `p`-torsion has the expected
cardinality `p²`, then `σ ^ (p (p − 1))` acts trivially on the WHOLE
`p`-torsion.

The `p²`-count is a hypothesis rather than an instance-derived fact so
that the caller can supply it in whichever form its ambient field
provides (`TorsionCard.card_torsionBy` for a separably closed `L`). -/
theorem WeierstrassCurve.point_map_pow_eq_self_of_eigenvector
    {K : Type*} [Field K] (X : WeierstrassCurve K)
    {L : Type*} [Field L] [Algebra K L] [DecidableEq L]
    {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card (AddSubgroup.torsionBy (X⁄L).Point ((p : ℕ) : ℤ)) = p ^ 2)
    (σ : L ≃ₐ[K] L)
    {Q : (X⁄L).Point} (hQtor : ((p : ℕ) : ℤ) • Q = 0) (hQ0 : Q ≠ 0)
    {c : ℕ} (hc : WeierstrassCurve.Affine.Point.map (W' := X) σ.toAlgHom Q = c • Q)
    (Q' : (X⁄L).Point) (hQ'tor : ((p : ℕ) : ℤ) • Q' = 0) :
    WeierstrassCurve.Affine.Point.map (W' := X)
      ((σ ^ (p * (p - 1)) : L ≃ₐ[K] L)).toAlgHom Q' = Q' := by
  classical
  have hmemiff : ∀ P : (X⁄L).Point,
      P ∈ AddSubgroup.torsionBy (X⁄L).Point ((p : ℕ) : ℤ) ↔ ((p : ℕ) : ℤ) • P = 0 :=
    fun P => Submodule.mem_torsionBy_iff _ _
  have hstab : ∀ P : (X⁄L).Point, ((p : ℕ) : ℤ) • P = 0 →
      WeierstrassCurve.Affine.Point.map (W' := X) σ.toAlgHom P ∈
        AddSubgroup.torsionBy (X⁄L).Point ((p : ℕ) : ℤ) := by
    intro P hP
    rw [hmemiff, ← map_zsmul, hP, map_zero]
  let ff : (AddSubgroup.torsionBy (X⁄L).Point ((p : ℕ) : ℤ)) →+
      (AddSubgroup.torsionBy (X⁄L).Point ((p : ℕ) : ℤ)) :=
    AddMonoidHom.mk'
      (fun P => ⟨WeierstrassCurve.Affine.Point.map (W' := X) σ.toAlgHom P.1,
        hstab P.1 ((hmemiff P.1).mp P.2)⟩)
      (fun P₁ P₂ => Subtype.ext (map_add _ _ _))
  have hffinj : Function.Injective ff := by
    intro x y hxy
    exact Subtype.ext (WeierstrassCurve.Affine.Point.map_injective (W' := X)
      (f := σ.toAlgHom) (congrArg Subtype.val hxy))
  have hexp : ∀ x : (AddSubgroup.torsionBy (X⁄L).Point ((p : ℕ) : ℤ)), (p : ℕ) • x = 0 :=
    fun x => AddSubgroup.torsionBy.nsmul x
  have hQ0' : (⟨Q, (hmemiff Q).mpr hQtor⟩ :
      (AddSubgroup.torsionBy (X⁄L).Point ((p : ℕ) : ℤ))) ≠ 0 := by
    intro h
    exact hQ0 (congrArg Subtype.val h)
  have hfQ : ff ⟨Q, (hmemiff Q).mpr hQtor⟩ =
      ((c : ℤ)) • (⟨Q, (hmemiff Q).mpr hQtor⟩ :
        (AddSubgroup.torsionBy (X⁄L).Point ((p : ℕ) : ℤ))) := by
    apply Subtype.ext
    show WeierstrassCurve.Affine.Point.map (W' := X) σ.toAlgHom Q = _
    rw [hc, AddSubgroup.coe_zsmul, natCast_zsmul]
  have hiter : ∀ (n : ℕ) (x : (AddSubgroup.torsionBy (X⁄L).Point ((p : ℕ) : ℤ))),
      ((ff : _ → _)^[n] x : (X⁄L).Point) =
        (fun R => WeierstrassCurve.Affine.Point.map (W' := X) σ.toAlgHom R)^[n] x.1 := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
      rfl
  have hkey := borel_bound_iterate_eq_self hp ff hffinj hexp hcard hQ0' hfQ
    ⟨Q', (hmemiff Q').mpr hQ'tor⟩
  rw [WeierstrassCurve.point_map_algEquiv_pow]
  have h2 := congrArg Subtype.val hkey
  rw [hiter] at h2
  exact h2

/-- **A root of unity congruent to `1` modulo an ideal is `1`** (PROVEN
2026-07-25): in a domain, if `ζ ^ m = 1`, if `ζ − 1` lies in an ideal `I`
and if the image of `m` does NOT lie in `I`, then `ζ = 1`. Proof:
`(∑_{i<m} ζ^i) (ζ − 1) = ζ^m − 1 = 0`, so in a domain either `ζ = 1` or
the geometric sum vanishes; but that sum is congruent to `m` modulo `I`
(each `ζ^i − 1` is a multiple of `ζ − 1`), and `m ∉ I`.

This is the ideal-theoretic form of "roots of unity of order prime to the
residue characteristic inject into the residue field", which is what makes
the tame character below well defined. -/
theorem eq_one_of_pow_eq_one_of_sub_one_mem {S : Type*} [CommRing S] [IsDomain S]
    {I : Ideal S} {ζ : S} {m : ℕ} (hζ : ζ ^ m = 1) (h1 : ζ - 1 ∈ I)
    (hm : ((m : ℕ) : S) ∉ I) : ζ = 1 := by
  have hgeom : (∑ i ∈ Finset.range m, ζ ^ i) * (ζ - 1) = 0 := by
    rw [geom_sum_mul, hζ, sub_self]
  rcases mul_eq_zero.mp hgeom with hsum | hsub
  · exfalso
    apply hm
    have hsplit : ∑ i ∈ Finset.range m, (ζ ^ i - 1) =
        (∑ i ∈ Finset.range m, ζ ^ i) - ((m : ℕ) : S) := by
      rw [Finset.sum_sub_distrib]
      simp
    have hmem : (∑ i ∈ Finset.range m, ζ ^ i) - ((m : ℕ) : S) ∈ I := by
      rw [← hsplit]
      refine Ideal.sum_mem _ fun i _ => ?_
      have hi : ζ ^ i - 1 = (∑ j ∈ Finset.range i, ζ ^ j) * (ζ - 1) := (geom_sum_mul ζ i).symm
      rw [hi]
      exact Ideal.mul_mem_left _ _ h1
    rw [hsum, zero_sub] at hmem
    simpa using (Ideal.neg_mem_iff _).mp hmem
  · exact sub_eq_zero.mp hsub

/-- **A natural number prime to `p` is a unit at the `p`-adic place**
(PROVEN 2026-07-25): `Valued.v (n : ℚ_p) = 1` when `p ∤ n`. The chain is
`p ∤ n → n ∈ (p)ᶜ → intValuation n = 1 → Valued.v (n : ℚ_p) = 1`, the last
step through `valuedAdicCompletion_eq_valuation`, with the numeral/instance
bridge pinning `instAlgebraAdicCompletion` exactly as in
`valued_natCast_adicCompletionIntegers_eq_one` (`GaloisRep.lean`), of which
this is the general-`n` version. -/
theorem valued_natCast_adicCompletionIntegers_eq_one_of_not_dvd {p : ℕ} (hp : p.Prime)
    {n : ℕ} (hpn : ¬ p ∣ n) :
    Valued.v (((n : ℕ) :
        IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat) :
      IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat) = 1 := by
  set v := hp.toHeightOneSpectrumRingOfIntegersRat
  have hcompl : ((n : ℕ) : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal.primeCompl := by
    intro hmem
    have hdvd := (Nat.Prime.mem_toHeightOneSpectrumRingOfIntegersRat_asIdeal hp _).mp hmem
    rw [map_natCast] at hdvd
    exact hpn (by exact_mod_cast hdvd)
  have hint1 : IsDedekindDomain.HeightOneSpectrum.intValuation v
      ((n : ℕ) : NumberField.RingOfIntegers ℚ) = 1 :=
    (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl
      v _).mpr hcompl
  have hK := (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation
      (v := v) (K := ℚ) ((n : ℕ) : NumberField.RingOfIntegers ℚ)).trans
    ((IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap
      (v := v) (K := ℚ) ((n : ℕ) : NumberField.RingOfIntegers ℚ)).trans hint1)
  have hbridge : (((n : ℕ) :
        IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v) :
      IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v) =
      @algebraMap _ _ _ _
        (IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
          (NumberField.RingOfIntegers ℚ) ℚ v)
        ((n : ℕ) : NumberField.RingOfIntegers ℚ) := by
    rw [map_natCast]
    rfl
  rw [hbridge]
  exact hK

/-- **A natural number prime to `p` avoids the maximal ideal of the
integral closure** (PROVEN 2026-07-25): by the previous lemma it is a unit
of `𝒪ᵥ`, hence a unit of `IntegralClosure 𝒪ᵥ ℚ̄_p`, hence outside that
ring's maximal ideal. This is the `m ∉ I` input of
`eq_one_of_pow_eq_one_of_sub_one_mem` in the transfer lemma below. -/
theorem natCast_notMem_maximalIdeal_integralClosure {p : ℕ} (hp : p.Prime)
    {n : ℕ} (hpn : ¬ p ∣ n) :
    ((n : ℕ) : IntegralClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat))) ∉
      IsLocalRing.maximalIdeal (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat))) := by
  set v := hp.toHeightOneSpectrumRingOfIntegersRat
  have hunit : IsUnit ((n : ℕ) :
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v) := by
    by_contra hnu
    have hmem := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have hlt := (IsDedekindDomain.HeightOneSpectrum.mem_completionIdeal_iff
      (K := ℚ) (v := v) _).mp hmem
    have h1 := valued_natCast_adicCompletionIntegers_eq_one_of_not_dvd hp hpn
    exact absurd (lt_of_lt_of_le hlt h1.symm.le) (lt_irrefl _)
  have hunitIC := hunit.map (algebraMap
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
    (IntegralClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))))
  rw [map_natCast] at hunitIC
  intro hmem
  exact ((IsLocalRing.mem_maximalIdeal _).mp hmem) hunitIC

open IsDedekindDomain in
/-- **Surjectivity of the tame character of local inertia, in ORBIT form**
(sorry node, cut 2026-07-25 out of
`exists_local_inertia_torsion_orbit_of_good_of_supersingular` below — the
LOCAL-FIELD half of that leaf, carrying no elliptic curve at all): let `p`
be a prime, `n` a natural number prime to `p`, and `ϖ ∈ ℚ̄_p` ANY `n`-th
root of `p`. Then some element `σ` of `localInertiaGroup p` has a
`⟨σ⟩`-orbit of length divisible by `n` on `ϖ`: `σ ^ k` fixes `ϖ` only when
`n ∣ k`.

WHY IT IS TRUE. `X ^ n − p` is Eisenstein over the discrete valuation ring
`𝒪^nr` (whose uniformizer is `p`), hence irreducible, so
`ℚ_p^nr(ϖ)/ℚ_p^nr` is totally ramified of degree `n`, and TAMELY so since
`p ∤ n`. It is Galois because `μ_n ⊂ ℚ_p^nr` (`n` is prime to `p` and the
residue field is `𝔽̄_p`, so Hensel lifts `μ_n`), and Kummer theory
identifies its Galois group with `μ_n`, cyclic of order `n`: a generator
`τ` satisfies `τ ϖ = ζ ϖ` with `ζ` a PRIMITIVE `n`-th root of unity, so
`τ ^ k ϖ = ζ ^ k ϖ = ϖ` forces `n ∣ k`. Any extension of `τ` to `ℚ̄_p`
fixes `ℚ_p^nr` pointwise, hence acts trivially on the residue field, hence
lies in `localInertiaGroup`. Serre, *Corps Locaux* IV §2; Neukirch II.7.7,
II.9.

Note the quantifier is over `localInertiaGroup` and must NOT be widened:
for an element of the full decomposition group the tame character is only
equivariant, not invariant, and the statement becomes false.

ROUTE for the next owner, staying at FINITE level — which avoids
formalising `ℚ_p^nr` itself:
1. `ℚ_p(μ_n)/ℚ_p` is unramified (`n` prime to `p`), and `X ^ n − p` is
   still Eisenstein over its valuation ring, so `M = ℚ_p(μ_n, ϖ)` is
   totally ramified of degree `n` over `ℚ_p(μ_n)`. Mathlib has Eisenstein
   irreducibility (`Polynomial.IsEisensteinAt.irreducible`).
2. `Gal(M/ℚ_p(μ_n))` is cyclic of order `n`, generated by `τ : ϖ ↦ ζ ϖ`
   for a primitive `ζ ∈ μ_n` (Kummer; the `IsPrimitiveRoot` API).
3. `τ` lies in the inertia subgroup of `Gal(M/ℚ_p)`: total ramification
   makes the residue field of `M` equal to that of `ℚ_p(μ_n)`, which `τ`
   fixes pointwise.
4. Lift to the full `localInertiaGroup` by the PROVEN compactness lifting
   `exists_mem_localInertiaGroup_restrictNormalHom_eq`
   (`Fermat/FLT/Deformations/RepresentationTheory/LocalInertiaFixedField.lean`,
   the profinite half of Neukirch II.9.11), and read the orbit condition
   back off `σ ^ k ϖ = ϖ ↔ ζ ^ k = 1`.

MISSING FROM MATHLIB, in dependency order, as statements: (a) *a totally
ramified extension of local fields has the same residue field* — in the
`ValuationSubring` decomposition/inertia vocabulary already used by
`mem_inertiaSubgroup_localValuationSubring`; (b) *Kummer theory over a
field containing `μ_n`*: `Gal(K(a^{1/n})/K) ≃ μ_n` by `τ ↦ τ(a^{1/n})/a^{1/n}`,
of which mathlib has the `IsPrimitiveRoot`/`X ^ n - C a` splitting pieces
but not the Galois-group identification. -/
theorem exists_localInertia_tameCharacter_orbit {p : ℕ} (hp : p.Prime) {n : ℕ}
    (hpn : ¬ p ∣ n)
    (ϖ : AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hp.toHeightOneSpectrumRingOfIntegersRat))
    (hϖ : ϖ ^ n = ((p : ℕ) : AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hp.toHeightOneSpectrumRingOfIntegersRat))) :
    ∃ σ ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat,
      ∀ k : ℕ,
        ((σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hp.toHeightOneSpectrumRingOfIntegersRat))
            ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
              hp.toHeightOneSpectrumRingOfIntegersRat]
            (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hp.toHeightOneSpectrumRingOfIntegersRat))) ^ k) ϖ = ϖ →
        n ∣ k :=
  sorry

open IsDedekindDomain in
set_option backward.isDefEq.respectTransparency false in
/-- **The tame character does not see units: an inertia element fixing a
value of the right valuation fixes the root** (PROVEN 2026-07-25): let
`p ∤ n`, let `ϖ` be an `n`-th root of `p` in `ℚ̄_p`, and let `z` satisfy
`|z ϖ| = 1` for the spectral norm — i.e. `z` has exactly the valuation of
`ϖ⁻¹`. If `σ ∈ localInertiaGroup p` fixes `z`, then `σ` fixes `ϖ`.

This is the bridge between the ARITHMETIC of a torsion point (whose
abscissa `z` carries the Newton-polygon valuation) and the LOCAL-FIELD
leaf above (which is about `ϖ`). Proof: `ζ = σϖ/ϖ` satisfies
`ζ ^ n = σ(ϖ^n)/ϖ^n = σ(p)/p = 1`; writing `w = z ϖ`, a unit of the
integral closure since `|w| = 1` (and so is `w⁻¹`), one has `σ w = ζ w`,
whence `ζ − 1 = (σ w − w) · w⁻¹` lies in the maximal ideal precisely
because `σ` is in INERTIA; and a root of unity of order prime to `p`
congruent to `1` modulo the maximal ideal is `1`
(`eq_one_of_pow_eq_one_of_sub_one_mem`, whose `n ∉ 𝔪` input is
`natCast_notMem_maximalIdeal_integralClosure`).

The hypothesis on `σ` is inertia and cannot be relaxed to the
decomposition group: a Frobenius lift moves `μ_n`, so `ζ` need not be
trivial modulo the maximal ideal. -/
theorem localInertia_fixes_tame_root_of_fixes {p : ℕ} (hp : p.Prime) {n : ℕ}
    (hpn : ¬ p ∣ n)
    {ϖ z : AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hp.toHeightOneSpectrumRingOfIntegersRat)}
    (hϖ : ϖ ^ n = ((p : ℕ) : AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hp.toHeightOneSpectrumRingOfIntegersRat)))
    (hzϖ : spectralNorm (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)) (z * ϖ) = 1)
    {σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat))
      ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat]
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat))}
    (hσ : σ ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat)
    (hfix : σ z = z) :
    σ ϖ = ϖ := by
  classical
  -- `n ≠ 0`, since `p ∣ 0`
  have hn0 : n ≠ 0 := by rintro rfl; exact hpn (dvd_zero p)
  -- nonvanishing
  have hw0 : z * ϖ ≠ 0 := by
    intro h
    rw [h, spectralNorm_zero] at hzϖ
    exact zero_ne_one hzϖ
  have hϖ0 : ϖ ≠ 0 := right_ne_zero_of_mul hw0
  have hz0 : z ≠ 0 := left_ne_zero_of_mul hw0
  -- the tame character value `ζ = σ ϖ / ϖ` is an `n`-th root of unity
  have hsp : σ ((p : ℕ) : AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hp.toHeightOneSpectrumRingOfIntegersRat)) =
      ((p : ℕ) : AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)) := map_natCast σ p
  have hϖn0 : ϖ ^ n ≠ 0 := pow_ne_zero _ hϖ0
  have hζpow : (σ ϖ / ϖ) ^ n = 1 := by
    rw [div_pow, ← map_pow, hϖ, hsp, ← hϖ, div_self hϖn0]
  have hsϖ : σ ϖ = (σ ϖ / ϖ) * ϖ := (div_mul_cancel₀ _ hϖ0).symm
  have hsw : σ (z * ϖ) = (σ ϖ / ϖ) * (z * ϖ) := by
    rw [map_mul, hfix]
    field_simp
  -- integrality of the unit `w = z ϖ`, of its inverse, and of `ζ`
  have hwint : IsIntegral (HeightOneSpectrum.adicCompletionIntegers ℚ
      hp.toHeightOneSpectrumRingOfIntegersRat) (z * ϖ) :=
    isIntegral_of_spectralNorm_le_one (le_of_eq hzϖ)
  have hwinvint : IsIntegral (HeightOneSpectrum.adicCompletionIntegers ℚ
      hp.toHeightOneSpectrumRingOfIntegersRat) (z * ϖ)⁻¹ := by
    refine isIntegral_of_spectralNorm_le_one (le_of_eq ?_)
    rw [spectralNorm_inv, hzϖ, inv_one]
  have hζint : IsIntegral (HeightOneSpectrum.adicCompletionIntegers ℚ
      hp.toHeightOneSpectrumRingOfIntegersRat) (σ ϖ / ϖ) := by
    refine ⟨Polynomial.X ^ n - 1, ?_, ?_⟩
    · have := Polynomial.monic_X_pow_sub_C (R := HeightOneSpectrum.adicCompletionIntegers ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat) (1 : _) (n := n) hn0
      simpa [Polynomial.C_1] using this
    · simp [Polynomial.eval₂_sub, hζpow]
  -- transport to the integral closure
  set W : IntegralClosure (HeightOneSpectrum.adicCompletionIntegers ℚ
    hp.toHeightOneSpectrumRingOfIntegersRat)
    (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hp.toHeightOneSpectrumRingOfIntegersRat)) := ⟨z * ϖ, hwint⟩ with hW
  set Wi : IntegralClosure (HeightOneSpectrum.adicCompletionIntegers ℚ
    hp.toHeightOneSpectrumRingOfIntegersRat)
    (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hp.toHeightOneSpectrumRingOfIntegersRat)) := ⟨(z * ϖ)⁻¹, hwinvint⟩ with hWi
  set Z : IntegralClosure (HeightOneSpectrum.adicCompletionIntegers ℚ
    hp.toHeightOneSpectrumRingOfIntegersRat)
    (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hp.toHeightOneSpectrumRingOfIntegersRat)) := ⟨σ ϖ / ϖ, hζint⟩ with hZ
  have hinj : Function.Injective (algebraMap (IntegralClosure
      (HeightOneSpectrum.adicCompletionIntegers ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)))
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat))) := fun _ _ h => Subtype.ext h
  have hvZ : algebraMap _ _ Z = σ ϖ / ϖ := by rw [hZ]; rfl
  have hvW : algebraMap _ _ W = z * ϖ := by rw [hW]; rfl
  have hvWi : algebraMap _ _ Wi = (z * ϖ)⁻¹ := by rw [hWi]; rfl
  have hvsW : algebraMap _ _ (σ • W) = σ (z * ϖ) := by rw [hW]; rfl
  have hZ1 : Z - 1 ∈ IsLocalRing.maximalIdeal (IntegralClosure
      (HeightOneSpectrum.adicCompletionIntegers ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat))) := by
    have hmem : σ • W - W ∈ IsLocalRing.maximalIdeal (IntegralClosure
        (HeightOneSpectrum.adicCompletionIntegers ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat)
        (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat))) := hσ W
    have hEq : Z - 1 = (σ • W - W) * Wi := by
      apply hinj
      rw [map_sub, map_mul, map_sub, map_one, hvZ, hvW, hvWi, hvsW, hsw]
      field_simp [hz0]
    rw [hEq]
    exact Ideal.mul_mem_right _ _ hmem
  have hZpow : Z ^ n = 1 := by
    apply hinj
    rw [map_pow, map_one, hvZ]
    exact hζpow
  have hZ0 : Z = 1 :=
    eq_one_of_pow_eq_one_of_sub_one_mem hZpow hZ1
      (natCast_notMem_maximalIdeal_integralClosure hp hpn)
  have hζ1 : σ ϖ / ϖ = 1 := by
    have h := congrArg (algebraMap (IntegralClosure
      (HeightOneSpectrum.adicCompletionIntegers ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)))
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat))) hZ0
    rw [hvZ, map_one] at h
    exact h
  rw [hsϖ, hζ1, one_mul]

open IsDedekindDomain in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
/-- **The Newton-polygon valuation of the abscissa of a local `p`-torsion
point at a good SUPERSINGULAR prime** (sorry node, cut 2026-07-25 out of
`exists_local_inertia_torsion_orbit_of_good_of_supersingular` below — the
ELLIPTIC-CURVE half of that leaf): if `E/ℚ` has good supersingular
reduction at `p` and `(x, y)` is an affine `p`-torsion point of the base
change to `ℚ̄_p`, then `|x| ^ (p² − 1) · |p| ^ 2 = 1` for the spectral
norm, i.e. `v(x) = −2/(p² − 1)`.

WHY IT IS TRUE. Supersingularity says the reduced curve has no nonzero
geometric `p`-torsion, so all of `E[p]` lies in the kernel of reduction,
i.e. in the `p`-torsion of the formal group, which has height `2`. The
Newton polygon of `[p](T) = pT + ⋯ + (unit) T^{p²} + ⋯` is then a single
segment of slope `1/(p² − 1)`: every nonzero point of `E[p]` has formal
parameter of valuation `1/(p² − 1)`, and since `t = −x/y` with
`v(x) = −2 v(t)`, `v(x) = −2/(p² − 1)`. Silverman *AEC* IV.2–IV.3, VII.6;
ATAEC IV.6.

ROUTE: the DIVISION-POLYNOMIAL route avoids formal groups altogether —
mathlib has `WeierstrassCurve.Ψ`/`preΨ`, and the content is that the
`p`-division polynomial has Newton polygon the single segment from
`(0, 0)` to `((p² − 1)/2, 1)`, so each root `x(Q)` has
`v(x) = −2/(p² − 1)`. Mathlib's `RingTheory/FormalGroup/Basic.lean` is
embryonic (group axioms only — no height, no `[p]`-series, no Newton
polygon), so the formal-group route would need that theory built first.
The sibling leaf `exists_localKernelDivision_of_good_reduction` (same
file) needs the same Newton polygon and should be read alongside this one.

NUMERICAL CERTIFICATE (PARI/GP, 2026-07-25 — a check of the STATEMENT,
not a proof): for `p = 5` and `E : y² = x³ + 1` (which has `v₅(Δ) = 0` and
`a₅ = 0`, i.e. good supersingular reduction at `5`) the `5`-division
polynomial has degree `12` with coefficient valuations `v₅ = 0, 2, 1, 1, 1`
at `x⁰, x³, x⁶, x⁹, x¹²`, so its Newton polygon at `5` is the SINGLE
segment from `(0,0)` to `(12,1)`: every root has valuation
`−1/12 = −2/(p² − 1)`, exactly as asserted. `factorpadic` moreover shows
that polynomial is irreducible over `ℚ₅`. The same check at `p = 7` with
`E : y² = x³ + x` gives degree `24 = (p² − 1)/2`, irreducible, with Newton
polygon the single segment `(0,0)–(24,1)`. -/
theorem WeierstrassCurve.spectralNorm_torsion_abscissa_of_good_of_supersingular
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : p.Prime)
    [E.HasGoodReduction
      (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)]
    (hss : ∀ P : ((E.reduction
        (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal))⁄
        (AlgebraicClosure (IsLocalRing.ResidueField
          (Localization.AtPrime
            hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)))).Point,
      (p : ℤ) • P = 0 → P = 0)
    (x y : AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hp.toHeightOneSpectrumRingOfIntegersRat))
    (h : ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
      (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat))).toAffine.Nonsingular x y)
    (htor : ((p : ℕ) : ℤ) • (WeierstrassCurve.Affine.Point.some x y h :
        ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
          (HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat))).Point) = 0) :
    spectralNorm (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)) x ^ (p ^ 2 - 1) *
      spectralNorm (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat))
      ((p : ℕ) : AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)) ^ 2 = 1 :=
  sorry

open ValuativeRel IsDedekindDomain in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
/-- **Serre's level-2 fundamental character, ONE-POINT form: an inertia
element whose orbit on some local `p`-torsion point has length divisible
by `p + 1`** (DERIVED 2026-07-25 over two bricks —
`WeierstrassCurve.spectralNorm_torsion_abscissa_of_good_of_supersingular`
(the ELLIPTIC-CURVE half: the Newton-polygon valuation of the abscissa,
steps 1–2 of the route below) and `exists_localInertia_tameCharacter_orbit`
(the LOCAL-FIELD half: surjectivity of the tame character, steps 3–4),
glued by the PROVEN `localInertia_fixes_tame_root_of_fixes`, which
transports a fixed abscissa to a fixed `n`-th root of `p`; the tame
exponent used here is `n = (p² − 1)/2`, prime to `p`, and
`(p + 1) ∣ (p² − 1)/2` for odd `p`. Originally cut 2026-07-25 out of
`exists_local_inertia_torsion_order_of_good_of_supersingular` below,
whose quantifier over the whole `p`-torsion MODULE it replaces by a
statement about a SINGLE point — that is the entire content of the cut,
and it is the shape the ramification argument actually produces): for an
elliptic curve over `ℚ` with good supersingular reduction at an odd
prime `p` there are an element `σ` of the local inertia at `p` and a
`p`-torsion point `Q` of the completed base change over the local
algebraic closure such that `σ ^ k` fixes `Q` only when `p + 1` divides
`k`.

`Q ≠ 0` is deliberately NOT among the conclusions, and dropping it costs
nothing: it is IMPLIED, because `σ ^ 1` fixes `0` while `p + 1 ∤ 1`. So
the statement is not vacuous — a junk witness `Q = 0` refutes its own
orbit condition.

WHY IT IS TRUE. Supersingularity puts all of `E[p]` inside the kernel of
reduction, i.e. inside the `p`-torsion of the formal group, which has
height `2`; the Newton polygon of `[p](T)` then has the single slope
`1/(p² − 1)`, so every nonzero point of `E[p]` generates a totally and
TAMELY ramified extension (`p ∤ p² − 1`) of ramification index divisible
by `p² − 1` over the maximal unramified extension of `ℚ_p`. Hence the
inertia image in `Aut(E[p]) ≅ GL₂(𝔽_p)` is the nonsplit Cartan subgroup
`𝔽_{p²}ˣ`, cyclic of order `p² − 1 = (p − 1)(p + 1)`, acting SIMPLY
TRANSITIVELY on the `p² − 1` nonzero points of `E[p]`. A generator `σ`
therefore has trivial stabilizer at every nonzero `Q`, so its orbit
there has length exactly `p² − 1`, and `σ ^ k Q = Q` forces
`(p² − 1) ∣ k`, a fortiori `(p + 1) ∣ k`. Serre, *Propriétés
galoisiennes des points d'ordre fini des courbes elliptiques*, Invent.
Math. 15 (1972), §1.9–1.12, Prop. 12; Silverman ATAEC IV.6, V.

ROUTE for the next owner, in the vocabulary this development already
has (2026-07-25):
1. *Containment in the kernel of reduction.* `hss` says the reduced
   curve has NO nonzero geometric `p`-torsion, so ANY reduction
   homomorphism kills `E[p]`; the sorried leaf
   `exists_localReductionHom_of_good_reduction` (same file) supplies
   the inertia-equivariant `red`, and this step is then immediate.
2. *The valuation of a `p`-torsion point.* mathlib has the division
   polynomials (`WeierstrassCurve.Ψ`, `preΨ`), and
   `AbsoluteGaloisGroup.lean` supplies `spectralNorm Kᵥ (Kᵥᵃˡᵍ)` as the
   absolute value on the local algebraic closure (together with
   `localValuationSubring` and its integral closure). The content to
   prove is that a root `x(Q)` of the `p`-division polynomial has
   `|x(Q)| = |p| ^ (−2/(p² − 1))`, i.e. the Newton-polygon slope. NOTE
   mathlib's `Mathlib/RingTheory/FormalGroup/Basic.lean` is embryonic
   (group axioms only — no height, no `[p]`-series, no Newton polygon),
   so the formal-group route needs that theory built first; the
   division-polynomial route avoids it.
3. *From ramification to an inertia element.* `p ∤ p² − 1`, so the
   extension is tame and its inertia group is cyclic of order divisible
   by `p² − 1`. NOTE the `x`-COORDINATE ALONE SUFFICES here, which cuts
   the work materially: the `p`-division polynomial gives
   `ℚ_p(x(Q))/ℚ_p` totally and tamely ramified of degree divisible by
   `(p² − 1)/2`, tame ramification makes its inertia CYCLIC, so a
   generator `σ` has an orbit of length divisible by `(p² − 1)/2` on the
   conjugates of `x(Q)`; the orbit of `Q` itself surjects equivariantly
   onto that one, hence has length divisible by `(p² − 1)/2` too, and
   `(p + 1) ∣ (p² − 1)/2 = (p + 1)(p − 1)/2` for odd `p`. So neither the
   `y`-coordinate, nor the full nonsplit Cartan, nor simple transitivity
   on `E[p] ∖ 0` has to be formalised — only the Newton polygon of the
   division polynomial and tameness.
4. *From a finite level to `localInertiaGroup`.* The PROVEN compactness
   lifting `exists_mem_localInertiaGroup_restrictNormalHom_eq`
   (`Fermat/FLT/Deformations/RepresentationTheory/LocalInertiaFixedField.lean`,
   the profinite half of Neukirch II.9.11) turns an inertia element at a
   finite Galois level `N` into an element of the FULL
   `localInertiaGroup` restricting to it — this is how the witness `σ`
   below is meant to be built, once `N` is taken to contain the
   coordinates of `Q`.

NUMERICAL CERTIFICATE for the route (PARI/GP, 2026-07-25 — a check of
the STATEMENT, not a proof): take `p = 5` and `E : y² = x³ + 1`, which
has `v₅(Δ) = 0` and `a₅ = 0`, i.e. good supersingular reduction at `5`.
Its `5`-division polynomial has degree `12` with coefficient valuations
`v₅ = 0, 2, 1, 1, 1` at `x⁰, x³, x⁶, x⁹, x¹²`, so its Newton polygon at
`5` is the SINGLE segment from `(0,0)` to `(12,1)`: every root has
valuation `−1/12 = −2/(p² − 1)`, as the height-`2` formal group
predicts. `factorpadic` moreover shows the polynomial is IRREDUCIBLE
over `ℚ₅`, so `ℚ₅(x(Q))` is totally ramified of degree
`12 = (p² − 1)/2`, tamely (`5 ∤ 12`), and the full point field has
`e = 24 = p² − 1`. Hence the tame inertia image is cyclic of order
divisible by `p² − 1` and the orbit of a nonzero `Q` has length
divisible by `p + 1 = 6`, which is what this leaf asserts.

The same check at `p = 7` with `E : y² = x³ + x` (supersingular since
`7 ≡ 3 mod 4`, `a₇ = 0`, `v₇(Δ) = 0`) gives a `7`-division polynomial of
degree `24 = (p² − 1)/2`, irreducible over `ℚ₇`, with Newton polygon the
single segment `(0,0)–(24,1)`: root valuation `−1/24 = −2/(p² − 1)`
again. So the slope is the general formula, not a coincidence of `p = 5`. -/
theorem WeierstrassCurve.exists_local_inertia_torsion_orbit_of_good_of_supersingular
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    [E.HasGoodReduction
      (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)]
    (hss : ∀ P : ((E.reduction
        (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal))⁄
        (AlgebraicClosure (IsLocalRing.ResidueField
          (Localization.AtPrime
            hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)))).Point,
      (p : ℤ) • P = 0 → P = 0) :
    ∃ σ ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat,
      ∃ Q : ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
          (HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat))).Point,
        ((p : ℕ) : ℤ) • Q = 0 ∧
        ∀ k : ℕ,
          WeierstrassCurve.Affine.Point.map
            (W' := E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
              hp.toHeightOneSpectrumRingOfIntegersRat)))
            ((σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                  hp.toHeightOneSpectrumRingOfIntegersRat))
                ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
                  hp.toHeightOneSpectrumRingOfIntegersRat]
                (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                  hp.toHeightOneSpectrumRingOfIntegersRat))) ^ k).toAlgHom Q = Q →
          (p + 1) ∣ k := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharZero (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hp.toHeightOneSpectrumRingOfIntegersRat)) :=
    ((algebraMap (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat))).charZero_iff
      (algebraMap (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat))).injective).mp inferInstance
  -- the tame exponent `n = (p² − 1)/2`
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hodd
  have hp2 : 2 ≤ p := hp.two_le
  have hntwice : 2 * ((p ^ 2 - 1) / 2) = p ^ 2 - 1 := by
    have h1 : p ^ 2 = 2 * ((p + 1) * m) + 1 := by subst hm; ring
    omega
  have harith : (p + 1) ∣ (p ^ 2 - 1) / 2 := by
    refine ⟨m, ?_⟩
    have h1 : p ^ 2 = 2 * ((p + 1) * m) + 1 := by subst hm; ring
    omega
  have hnpos : 0 < (p ^ 2 - 1) / 2 := by
    have h1 : p ^ 2 = 2 * ((p + 1) * m) + 1 := by subst hm; ring
    have h2 : 1 ≤ (p + 1) * m := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega))
    omega
  have hpn : ¬ p ∣ (p ^ 2 - 1) / 2 := by
    intro hdvd
    have hone : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h1 : p ^ 2 = 2 * ((p ^ 2 - 1) / 2) + 1 := by omega
    have hd2 : p ∣ 2 * ((p ^ 2 - 1) / 2) := Dvd.dvd.mul_left hdvd 2
    have hdp2 : p ∣ p ^ 2 := dvd_pow_self p (by norm_num)
    rw [h1] at hdp2
    have hone' : p ∣ 1 := (Nat.dvd_add_right hd2).mp hdp2
    exact absurd (Nat.le_of_dvd one_pos hone') (by omega)
  -- a nonzero local `p`-torsion point
  have hcard : Nat.card (AddSubgroup.torsionBy
      ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat))).Point ((p : ℕ) : ℤ)) = p ^ 2 :=
    TorsionCard.card_torsionBy
      ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat))).map
        (algebraMap (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat)
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat)))) p
      (Nat.cast_ne_zero.mpr hp.ne_zero)
  haveI hnt : Nontrivial (AddSubgroup.torsionBy
      ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat))).Point ((p : ℕ) : ℤ)) := by
    have hne : Nat.card (AddSubgroup.torsionBy
        ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
          (HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat))).Point ((p : ℕ) : ℤ)) ≠ 0 := by
      rw [hcard]
      exact pow_ne_zero _ hp.ne_zero
    obtain ⟨hnonempty, hfinite⟩ := Nat.card_ne_zero.mp hne
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    have h1 := @Nat.card_unique _ hnonempty hsub
    rw [hcard] at h1
    nlinarith [hp.two_le]
  obtain ⟨QT, hQne⟩ := exists_ne (0 : AddSubgroup.torsionBy
      ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat))).Point ((p : ℕ) : ℤ))
  obtain ⟨Q, hQmem⟩ := QT
  have hQ0 : Q ≠ 0 := fun hh => hQne (Subtype.ext hh)
  have hQtor : ((p : ℕ) : ℤ) • Q = 0 := (Submodule.mem_torsionBy_iff _ _).mp hQmem
  clear hQmem hQne hnt hcard
  rcases Q with _ | ⟨x, y, hxy⟩
  · exact absurd rfl hQ0
  -- the Newton-polygon value of the abscissa, and a compatible `n`-th root of `p`
  have hval := E.spectralNorm_torsion_abscissa_of_good_of_supersingular hp hss x y hxy hQtor
  obtain ⟨ϖ, hϖ⟩ := IsAlgClosed.exists_pow_nat_eq
    (((p : ℕ) : AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hp.toHeightOneSpectrumRingOfIntegersRat))) hnpos
  have hxϖ : spectralNorm (HeightOneSpectrum.adicCompletion ℚ
      hp.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)) (x * ϖ) = 1 := by
    have hmul : spectralNorm (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat)
        (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat)) (x * ϖ) =
        spectralNorm (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat)
        (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat)) x *
        spectralNorm (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat)
        (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat)) ϖ :=
      spectralAlgNorm_mul (K := HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat) x ϖ
    have hpow := isPowMul_spectralNorm (K := HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)
      (L := AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)) ϖ hnpos
    rw [hϖ] at hpow
    have hnn : (0:ℝ) ≤ spectralNorm (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)) (x * ϖ) :=
      spectralNorm_nonneg (K := HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat) _
    have hval' : spectralNorm (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)) x ^ (2 * ((p ^ 2 - 1) / 2)) *
      spectralNorm (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat))
      ((p : ℕ) : AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)) ^ 2 = 1 := by
      rw [hntwice]; exact hval
    have hb : spectralNorm (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)) ϖ ^ (2 * ((p ^ 2 - 1) / 2)) =
      (spectralNorm (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)) ϖ ^ ((p ^ 2 - 1) / 2)) ^ 2 := by
      rw [mul_comm, pow_mul]
    have hkey : (spectralNorm (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)) (x * ϖ)) ^ (2 * ((p ^ 2 - 1) / 2)) = 1 := by
      rw [hmul, mul_pow, hb, ← hpow]
      exact hval'
    rcases pow_eq_one_iff_cases.mp hkey with h | h | h
    · omega
    · exact h
    · exfalso; rw [h.1] at hnn; linarith
  -- the tame inertia element and the transfer of its orbit
  obtain ⟨σ, hσI, hσk⟩ := exists_localInertia_tameCharacter_orbit hp hpn ϖ hϖ
  refine ⟨σ, hσI, WeierstrassCurve.Affine.Point.some x y hxy, hQtor, ?_⟩
  intro k hk
  rw [WeierstrassCurve.Affine.Point.map_some] at hk
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at hk
  refine harith.trans (hσk k ?_)
  exact localInertia_fixes_tame_root_of_fixes hp hpn hϖ hxϖ (pow_mem hσI k) hk.1

open ValuativeRel IsDedekindDomain in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
/-- **Serre's level-2 fundamental character: an inertia element whose
action on the local `p`-torsion has order divisible by `p + 1`**
(DERIVED 2026-07-25 from the one-point leaf
`exists_local_inertia_torsion_orbit_of_good_of_supersingular`
immediately above: an exponent killing the whole `p`-torsion in
particular fixes the single point `Q` that leaf supplies. Cut
2026-07-25 out of
`not_local_inertia_eigenvector_of_good_of_supersingular` — the
*arithmetic* brick of the supersingular case, and since 2026-07-25 the
ONLY open brick of it: the *linear-algebra* brick, the Borel bound, is
PROVEN inside that theorem's proof from
`WeierstrassCurve.point_map_pow_eq_self_of_eigenvector`): for an
elliptic curve over `ℚ` with good supersingular
reduction at an odd prime `p` there is an element `σ` of the local
inertia at `p` such that no power `σ ^ k` with `p + 1 ∤ k` acts
trivially on the local `p`-torsion.

This is the group-order half of Serre, *Propriétés galoisiennes des
points d'ordre fini des courbes elliptiques*, Invent. Math. 15 (1972),
§1.9–1.12, Prop. 12. Supersingularity puts all of `E[p]` inside the
kernel of reduction, i.e. inside the `p`-torsion of the formal group,
which has height `2`; the Newton polygon of `[p](T)` then has the single
slope `1/(p² − 1)`, so every nonzero point of `E[p]` generates a totally
ramified extension of degree divisible by `(p² − 1)/2` of the
unramified quadratic extension of `ℚ_p`. Consequently the inertia image
in `Aut(E[p]) ≅ GL₂(𝔽_p)` contains the full nonsplit Cartan subgroup
`𝔽_{p²}ˣ` — inertia acts through the level-2 fundamental character
`φ₂`, whose image is cyclic of order `p² − 1 = (p − 1)(p + 1)` — and a
generator `σ` of the tame quotient has order exactly `p² − 1` on
`E[p]`; the conclusion below records only the divisibility by `p + 1`,
which is what the eigenvector contradiction needs. Silverman ATAEC
IV.6, V; Serre, op. cit.

ROUTE NOTE (2026-07-25): the conclusion is deliberately WEAKER than
"`σ` has order exactly `p² − 1` on `E[p]`" — it does not ask for the
minimality of the order, only that the set of exponents killing the
whole `p`-torsion is contained in `(p + 1)ℤ`. Proving the sharp
statement and then quoting `orderOf_dvd_iff_pow_eq_one` together with
`(p + 1) ∣ (p² − 1)` is a legitimate route, but it is strictly more work
than what the consumer needs; the consumer only ever instantiates `k` at
`k = p (p − 1)`. -/
theorem WeierstrassCurve.exists_local_inertia_torsion_order_of_good_of_supersingular
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    [E.HasGoodReduction
      (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)]
    (hss : ∀ P : ((E.reduction
        (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal))⁄
        (AlgebraicClosure (IsLocalRing.ResidueField
          (Localization.AtPrime
            hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)))).Point,
      (p : ℤ) • P = 0 → P = 0) :
    ∃ σ ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat,
      ∀ k : ℕ,
        (∀ Q : ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
            (HeightOneSpectrum.adicCompletion ℚ
              hp.toHeightOneSpectrumRingOfIntegersRat))).Point,
          ((p : ℕ) : ℤ) • Q = 0 →
          WeierstrassCurve.Affine.Point.map
            (W' := E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
              hp.toHeightOneSpectrumRingOfIntegersRat)))
            ((σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                  hp.toHeightOneSpectrumRingOfIntegersRat))
                ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
                  hp.toHeightOneSpectrumRingOfIntegersRat]
                (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                  hp.toHeightOneSpectrumRingOfIntegersRat))) ^ k).toAlgHom Q = Q) →
        (p + 1) ∣ k := by
  obtain ⟨σ, hσI, Q, hQtor, hQorb⟩ :=
    E.exists_local_inertia_torsion_orbit_of_good_of_supersingular hp hodd hss
  exact ⟨σ, hσI, fun k hk => hQorb k (hk Q hQtor)⟩

open ValuativeRel IsDedekindDomain in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
/-- **No local inertia eigenvector at a good SUPERSINGULAR prime**
(no DIRECT sorry since 2026-07-25: the linear-algebra `hborel` step
inside the proof is now PROVEN, and the only remaining gap is the
arithmetic brick
`exists_local_inertia_torsion_order_of_good_of_supersingular`; cut
2026-07-23 at the same local seam as the multiplicative and ordinary
quotients):
for an elliptic curve over `ℚ` with good supersingular reduction at an
odd prime `p` (supersingularity stated as the triviality of the
geometric `p`-torsion of the reduced curve `Ẽ/𝔽_p`), no nonzero
`p`-torsion point of the completed base change over the local
algebraic closure is an eigenvector of the local inertia: inertia acts
on the local `p`-torsion through the level-2 fundamental character of
the quadratic unramified extension, whose eigenvalues are
`𝔽_{p²}`-conjugate and not `𝔽_p`-rational. Serre, Propriétés
galoisiennes des points d'ordre fini des courbes elliptiques, Invent.
Math. 15 (1972), §1.11–1.12, Prop. 12. -/
theorem WeierstrassCurve.not_local_inertia_eigenvector_of_good_of_supersingular
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    [E.HasGoodReduction
      (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)]
    (hss : ∀ P : ((E.reduction
        (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal))⁄
        (AlgebraicClosure (IsLocalRing.ResidueField
          (Localization.AtPrime
            hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)))).Point,
      (p : ℤ) • P = 0 → P = 0)
    (Q : ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat))).Point)
    (hQtor : ((p : ℕ) : ℤ) • Q = 0) (hQ0 : Q ≠ 0)
    (heig : ∀ σ ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat,
      ∃ c : ZMod p,
        WeierstrassCurve.Affine.Point.map
          (W' := E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat)))
          ((σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hp.toHeightOneSpectrumRingOfIntegersRat))
            ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
              hp.toHeightOneSpectrumRingOfIntegersRat]
            (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hp.toHeightOneSpectrumRingOfIntegersRat)))).toAlgHom Q =
        c.val • Q) :
    False := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharZero (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hp.toHeightOneSpectrumRingOfIntegersRat)) :=
    ((algebraMap (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat))).charZero_iff
      (algebraMap (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat))).injective).mp inferInstance
  -- the `p²`-count of the local `p`-torsion, the input of the Borel bound
  have hcard : Nat.card (AddSubgroup.torsionBy
      ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat))).Point ((p : ℕ) : ℤ)) = p ^ 2 :=
    TorsionCard.card_torsionBy
      ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat))).map
        (algebraMap (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat)
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat)))) p
      (Nat.cast_ne_zero.mpr hp.ne_zero)
  -- ARITHMETIC BRICK (Serre's level-2 fundamental character): an inertia element whose
  -- action on the local `p`-torsion has order divisible by `p + 1`.
  obtain ⟨σ, hσI, hσord⟩ :=
    E.exists_local_inertia_torsion_order_of_good_of_supersingular hp hodd hss
  -- LINEAR-ALGEBRA BRICK (the Borel bound): if some nonzero `p`-torsion point is an
  -- eigenvector of the whole inertia, then the line it spans is inertia-stable, so every
  -- inertia element acts on the `2`-dimensional `𝔽_p`-space `E[p]` (of cardinality `p²`,
  -- `TorsionCard.card_torsionBy`) by an upper-triangular matrix `[[χ, α], [0, ψ]]` in a
  -- basis `(Q, w)` with `w ∉ ⟨Q⟩`. Since `χ, ψ ∈ 𝔽_pˣ` satisfy `χ ^ (p - 1) = ψ ^ (p - 1)
  -- = 1` (Fermat), the `(p - 1)`-st power of any inertia element is unipotent, hence
  -- killed by a further `p`-th power: the whole inertia acts through a group of exponent
  -- dividing `p * (p - 1)`.
  have hborel : σ ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat →
      (∀ σ' ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat,
        ∃ c : ZMod p,
          WeierstrassCurve.Affine.Point.map
            (W' := E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
              hp.toHeightOneSpectrumRingOfIntegersRat)))
            ((σ' : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat))
              ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat]
              (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat)))).toAlgHom Q =
          c.val • Q) →
      ((p : ℕ) : ℤ) • Q = 0 → Q ≠ 0 →
      ∀ Q' : ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
          (HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat))).Point,
        ((p : ℕ) : ℤ) • Q' = 0 →
        WeierstrassCurve.Affine.Point.map
          (W' := E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat)))
          ((σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat))
              ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat]
              (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat))) ^
            (p * (p - 1))).toAlgHom Q' = Q' := by
    intro hσI' heig' hQtor' hQ0' Q' hQ'tor
    obtain ⟨c, hc⟩ := heig' σ hσI'
    exact WeierstrassCurve.point_map_pow_eq_self_of_eigenvector
      (E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat))) hp hcard
      ((σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat))
        ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat]
        (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat))))
      hQtor' hQ0' hc Q' hQ'tor
  -- `p + 1` does not divide `p * (p - 1)`: the product is `2` modulo `p + 1`
  have harith : ¬ ((p + 1) ∣ p * (p - 1)) := by
    intro hdvd
    have h2 := hp.two_le
    have h3 : 3 ≤ p := by omega
    have hid : p * (p - 1) = (p + 1) * (p - 2) + 2 := by
      obtain ⟨q, hq⟩ : ∃ q, p = q + 3 := ⟨p - 3, by omega⟩
      rw [hq]
      have e1 : q + 3 - 1 = q + 2 := by omega
      have e2 : q + 3 - 2 = q + 1 := by omega
      rw [e1, e2]
      ring
    rw [hid] at hdvd
    have h4 : (p + 1) ∣ 2 := by
      have h5 := Nat.dvd_sub hdvd (dvd_mul_right (p + 1) (p - 2))
      rwa [Nat.add_sub_cancel_left] at h5
    have h6 := Nat.le_of_dvd (by norm_num) h4
    omega
  exact harith (hσord (p * (p - 1)) (hborel hσI heig hQtor hQ0))

open IsDedekindDomain in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **No inertia-stable line at a good SUPERSINGULAR prime** (DERIVED
2026-07-23 from the local eigenvector leaf
`not_local_inertia_eigenvector_of_good_of_supersingular` by
transporting a generator of the stable line along the chosen embedding
`ℚ̄ ↪ ℚ̂̄_p`): for an elliptic curve over `ℚ` with good supersingular
reduction at an odd prime `p`, no line of `E[p]` is stable under the
local inertia at `p`. A stable line has a generator `w ≠ 0` with
`W = span {w}`, so inertia moves `w` to scalar multiples of itself;
the transported point `Q = ι(w)` is then a nonzero `p`-torsion local
inertia EIGENVECTOR (equivariance of the transport:
`point_map_algClosureEmbeddingRat_comm`), which the local leaf
forbids. Serre, Propriétés galoisiennes…, Invent. Math. 15 (1972),
§1.11–1.12, Prop. 12. -/
theorem WeierstrassCurve.not_inertia_stable_line_of_good_of_supersingular
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    [E.HasGoodReduction
      (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)]
    (hss : ∀ P : ((E.reduction
        (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal))⁄
        (AlgebraicClosure (IsLocalRing.ResidueField
          (Localization.AtPrime
            hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)))).Point,
      (p : ℤ) • P = 0 → P = 0)
    (W : Submodule (ZMod p) ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p))
    (hW1 : Module.finrank (ZMod p) W = 1)
    (hWstable : ∀ σ ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat,
      ∀ v ∈ W, E.galoisRep p hp.pos
        ((Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat))) σ) v ∈ W) :
    False := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  letI := algebraRatAlgClosureAdic hp.toHeightOneSpectrumRingOfIntegersRat
  haveI hfinG : Finite ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p) :=
    Nat.finite_of_card_ne_zero (by
      rw [TorsionCard.card_torsionBy (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) p
        (Nat.cast_ne_zero.mpr hp.ne_zero)]
      exact pow_ne_zero 2 hp.ne_zero)
  haveI : Fintype ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p) :=
    Fintype.ofFinite _
  haveI : Module.Finite (ZMod p)
      ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p) :=
    Module.Finite.of_finite
  -- a generator of the stable line
  have hWbot : W ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hW1
    exact zero_ne_one hW1
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWbot
  have hspan : Submodule.span (ZMod p) {w} = W := by
    apply Submodule.eq_of_le_of_finrank_le
      ((Submodule.span_singleton_le_iff_mem w W).mpr hwW)
    rw [hW1, finrank_span_singleton hw0]
  have hWmem : ∀ u ∈ W, ∃ c : ZMod p, u = c • w := by
    intro u hu
    rw [← hspan] at hu
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hu
    exact ⟨c, hc.symm⟩
  -- transport the generator to the local `p`-torsion and apply the leaf
  refine E.not_local_inertia_eigenvector_of_good_of_supersingular hp hodd hss
    (show ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat))).Point from
      WeierstrassCurve.Affine.Point.map (W' := E)
        (algClosureEmbeddingRat hp.toHeightOneSpectrumRingOfIntegersRat)
        (show ((E)⁄(AlgebraicClosure ℚ)).Point from w.1)) ?_ ?_ ?_
  · -- the transported point is `p`-torsion
    have h1 : ((p : ℕ) : ℤ) •
        (show ((E)⁄(AlgebraicClosure ℚ)).Point from w.1) = 0 := by
      have h0 := w.2
      rw [Submodule.mem_torsionBy_iff] at h0
      exact h0
    show ((p : ℕ) : ℤ) • WeierstrassCurve.Affine.Point.map (W' := E)
        (algClosureEmbeddingRat hp.toHeightOneSpectrumRingOfIntegersRat)
        (show ((E)⁄(AlgebraicClosure ℚ)).Point from w.1) = 0
    rw [← map_zsmul, h1, map_zero]
  · -- the transported point is nonzero
    intro h
    apply hw0
    apply Subtype.ext
    show (show ((E)⁄(AlgebraicClosure ℚ)).Point from w.1) = 0
    apply WeierstrassCurve.Affine.Point.map_injective
      (f := algClosureEmbeddingRat hp.toHeightOneSpectrumRingOfIntegersRat)
    rw [map_zero]
    exact h
  · -- the transported point is an inertia eigenvector
    intro σ hσ
    obtain ⟨c, hc⟩ := hWmem _ (hWstable σ hσ w hwW)
    refine ⟨c, ?_⟩
    -- the stability relation with a `ℕ`-scalar
    have h1 : E.galoisRep p hp.pos
        ((Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat))) σ) w = c.val • w := by
      rw [hc]
      conv_lhs => rw [← show ((c.val : ℕ) : ZMod p) = c from by
        rw [ZMod.natCast_val, ZMod.cast_id]]
      rw [Nat.cast_smul_eq_nsmul]
    -- … at the level of underlying points
    have hcoe : (show ((E)⁄(AlgebraicClosure ℚ)).Point from
        (E.galoisRep p hp.pos
          ((Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hp.toHeightOneSpectrumRingOfIntegersRat))) σ) w).1) =
        c.val • (show ((E)⁄(AlgebraicClosure ℚ)).Point from w.1) := by
      rw [h1]
      push_cast
      rfl
    have hb : (show ((E)⁄(AlgebraicClosure ℚ)).Point from
        (E.galoisRep p hp.pos
          ((Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hp.toHeightOneSpectrumRingOfIntegersRat))) σ) w).1) =
        WeierstrassCurve.Affine.Point.map
          (((Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hp.toHeightOneSpectrumRingOfIntegersRat))) σ :
            AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom
          (show ((E)⁄(AlgebraicClosure ℚ)).Point from w.1) := rfl
    have hcomm := point_map_algClosureEmbeddingRat_comm
      hp.toHeightOneSpectrumRingOfIntegersRat E σ
      (show ((E)⁄(AlgebraicClosure ℚ)).Point from w.1)
    -- identify the `σ`-action on the mapped curve with `algClosureSigmaRat`
    have hbb : ∀ Qp : ((E)⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat))).Point,
        WeierstrassCurve.Affine.Point.map (W' := E)
          (algClosureSigmaRat hp.toHeightOneSpectrumRingOfIntegersRat σ) Qp =
        (show ((E)⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat))).Point from
          WeierstrassCurve.Affine.Point.map
            (W' := E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
              hp.toHeightOneSpectrumRingOfIntegersRat)))
            ((σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat))
              ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat]
              (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat)))).toAlgHom
            (show ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
              hp.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat))).Point from Qp)) := by
      intro Qp
      cases Qp with
      | zero => rfl
      | some x y h => rfl
    -- assemble: `σ` after transport = transport after global `σ`
    --           = the `c.val`-multiple of the transport
    have hstep : WeierstrassCurve.Affine.Point.map (W' := E)
        (algClosureSigmaRat hp.toHeightOneSpectrumRingOfIntegersRat σ)
        (WeierstrassCurve.Affine.Point.map (W' := E)
          (algClosureEmbeddingRat hp.toHeightOneSpectrumRingOfIntegersRat)
          (show ((E)⁄(AlgebraicClosure ℚ)).Point from w.1)) =
        c.val • WeierstrassCurve.Affine.Point.map (W' := E)
          (algClosureEmbeddingRat hp.toHeightOneSpectrumRingOfIntegersRat)
          (show ((E)⁄(AlgebraicClosure ℚ)).Point from w.1) := by
      rw [← hcomm, ← hb, hcoe, map_nsmul]
    rw [hbb] at hstep
    exact hstep

set_option backward.isDefEq.respectTransparency false in
/-- **The connected-étale line at a good prime, given an
inertia-stable line** (DERIVED 2026-07-23 from the ordinary leaf
`exists_etale_line_of_good_of_ordinary` and the supersingular leaf
`not_inertia_stable_line_of_good_of_supersingular`, by the tautological
fork on the vanishing of the reduced curve's geometric `p`-torsion):
for an elliptic curve over `ℚ` with good reduction at an odd prime
`p`, if SOME line `W` of `E[p]` is stable under the local inertia at
`p`, then there is a line `L ⊆ E[p]` (the connected line of the
connected-étale sequence — not necessarily `W`) such that inertia at
`p` acts trivially on `E[p]/L`. If the reduction has a nonzero
geometric `p`-torsion point (ordinary), the first leaf answers
directly; if not (supersingular), the second leaf refutes the given
stable line. Serre Duke 1987, §4.1; Silverman ATAEC V. -/
theorem WeierstrassCurve.exists_etale_line_of_good_of_inertia_stable_line
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    [E.HasGoodReduction
      (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)]
    (W : Submodule (ZMod p) ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p))
    (hW1 : Module.finrank (ZMod p) W = 1)
    (hWstable : ∀ σ ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat,
      ∀ v ∈ W, E.galoisRep p hp.pos
        ((Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat))) σ) v ∈ W) :
    ∃ L : Submodule (ZMod p) ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p),
      Module.finrank (ZMod p) L = 1 ∧
      ∀ σ ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat,
        ∀ v, L.mkQ (E.galoisRep p hp.pos
            ((Field.absoluteGaloisGroup.map (algebraMap ℚ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat))) σ) v) = L.mkQ v := by
  by_cases hord : ∃ P : ((E.reduction
      (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal))⁄
      (AlgebraicClosure (IsLocalRing.ResidueField
        (Localization.AtPrime
          hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)))).Point,
      P ≠ 0 ∧ (p : ℤ) • P = 0
  · exact E.exists_etale_line_of_good_of_ordinary hp hodd hord
  · -- no nonzero geometric `p`-torsion downstairs: supersingular
    have hss : ∀ P : ((E.reduction
        (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal))⁄
        (AlgebraicClosure (IsLocalRing.ResidueField
          (Localization.AtPrime
            hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)))).Point,
        (p : ℤ) • P = 0 → P = 0 := by
      intro P hP
      by_contra hne
      exact hord ⟨P, hne, hP⟩
    exact (E.not_inertia_stable_line_of_good_of_supersingular hp hodd hss
      W hW1 hWstable).elim

set_option backward.isDefEq.respectTransparency false in
/-- **The connected-étale dichotomy at a good prime** (DERIVED
2026-07-23 from the sharper leaf
`exists_etale_line_of_good_of_inertia_stable_line` by the tautological
fork on the existence of an INERTIA-stable line — the discriminant of
the ordinary/supersingular dichotomy at the representation level): for
an elliptic curve over `ℚ` with good reduction at an odd prime `p`,
EITHER there is a line `L ⊆ E[p]` such that the local inertia at `p`
acts trivially on `E[p]/L`, OR no line of `E[p]` is stable under the
full mod-`p` representation. If some inertia-stable line exists, the
leaf provides the étale line; if none does, then a fortiori no line is
stable under the full representation (restrict to inertia). Serre,
Propriétés galoisiennes…, Invent. Math. 15 (1972), §1.11–1.12,
Prop. 12; Serre Duke 1987, §4.1. -/
theorem WeierstrassCurve.exists_etale_line_or_no_stable_line_of_good
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    [E.HasGoodReduction
      (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)] :
    (∃ L : Submodule (ZMod p) ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p),
      Module.finrank (ZMod p) L = 1 ∧
      ∀ σ ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat,
        ∀ v, L.mkQ (E.galoisRep p hp.pos
            ((Field.absoluteGaloisGroup.map (algebraMap ℚ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat))) σ) v) = L.mkQ v) ∨
    (∀ W : Submodule (ZMod p)
        ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p),
      Module.finrank (ZMod p) W = 1 →
      ¬ ∀ g v, v ∈ W → E.galoisRep p hp.pos g v ∈ W) := by
  classical
  by_cases hI : ∃ W : Submodule (ZMod p)
      ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p),
    Module.finrank (ZMod p) W = 1 ∧
    ∀ σ ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat,
      ∀ v ∈ W, E.galoisRep p hp.pos
        ((Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat))) σ) v ∈ W
  · obtain ⟨W, hW1, hWst⟩ := hI
    exact Or.inl
      (E.exists_etale_line_of_good_of_inertia_stable_line hp hodd W hW1 hWst)
  · refine Or.inr fun W hW1 hstable => ?_
    exact hI ⟨W, hW1, fun σ _ v hv => hstable _ v hv⟩

set_option backward.isDefEq.respectTransparency false in
/-- **The connected-étale line at `p`, good case** (DERIVED 2026-07-22
from the dichotomy leaf `exists_etale_line_or_no_stable_line_of_good`:
the given stable line refutes the second disjunct): for an elliptic
curve over `ℚ` with good reduction at an odd prime `p` whose mod-`p`
representation admits a stable line, there is a line `L ⊆ E[p]` such
that the local inertia at `p` acts trivially on `E[p]/L`. Serre Duke
1987, §4.1. -/
theorem WeierstrassCurve.exists_etale_line_of_good_of_stable_line
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    [E.HasGoodReduction
      (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)]
    (W : Submodule (ZMod p) ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p))
    (hW1 : Module.finrank (ZMod p) W = 1)
    (hstable : ∀ g v, v ∈ W → E.galoisRep p hp.pos g v ∈ W) :
    ∃ L : Submodule (ZMod p) ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p),
      Module.finrank (ZMod p) L = 1 ∧
      ∀ σ ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat,
        ∀ v, L.mkQ (E.galoisRep p hp.pos
            ((Field.absoluteGaloisGroup.map (algebraMap ℚ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat))) σ) v) = L.mkQ v := by
  rcases E.exists_etale_line_or_no_stable_line_of_good hp hodd with h | h
  · exact h
  · exact absurd hstable (h W hW1)

set_option backward.isDefEq.respectTransparency false in
/-- **Linear algebra of the étale line** (PROVEN 2026-07-22): given the
stable line `W` with its characters and ANY line `L` on whose quotient
the inertia at `p` acts trivially, one of `χ₁`, `χ₂` is unramified at
`p`. If `W = L`, the quotient character `χ₂` is trivial on inertia
directly; if `W ≠ L`, the two lines of the 2-dimensional space meet
trivially, so a nonzero vector of `W` has nonzero image in the quotient
by `L`, and comparing the scalar action `χ₁` with the trivial quotient
action kills `χ₁` on inertia. -/
lemma FreyPackage.character_unramified_at_p_of_etale_line
    (P : FreyPackage)
    (W L : Submodule (ZMod P.p)
      ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p))
    (hW1 : Module.finrank (ZMod P.p) W = 1)
    (hL1 : Module.finrank (ZMod P.p) L = 1)
    (χ₁ χ₂ : Field.absoluteGaloisGroup ℚ →* (ZMod P.p)ˣ)
    (hχ₁ : ∀ g, ∀ v ∈ W,
      P.freyCurve.galoisRep P.p P.hppos g v = (χ₁ g : ZMod P.p) • v)
    (hχ₂ : ∀ g v, W.mkQ (P.freyCurve.galoisRep P.p P.hppos g v) =
      (χ₂ g : ZMod P.p) • W.mkQ v)
    (hL : ∀ σ ∈ localInertiaGroup P.pp.toHeightOneSpectrumRingOfIntegersRat,
      ∀ v, L.mkQ (P.freyCurve.galoisRep P.p P.hppos
          ((Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              P.pp.toHeightOneSpectrumRingOfIntegersRat))) σ) v) = L.mkQ v) :
    (localInertiaGroup P.pp.toHeightOneSpectrumRingOfIntegersRat ≤
      (χ₁.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          P.pp.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker) ∨
    (localInertiaGroup P.pp.toHeightOneSpectrumRingOfIntegersRat ≤
      (χ₂.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          P.pp.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker) := by
  classical
  haveI : Fact P.p.Prime := ⟨P.pp⟩
  -- finiteness bookkeeping: the torsion space has rank `2`
  have hcard : Nat.card
      ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) =
      P.p ^ 2 :=
    TorsionCard.card_torsionBy
      (P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))) P.p
      (Nat.cast_ne_zero.mpr P.pp.ne_zero)
  haveI hfin : Finite
      ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) :=
    Nat.finite_of_card_ne_zero (by
      rw [hcard]
      have := P.pp.pos
      positivity)
  haveI : Fintype
      ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) :=
    Fintype.ofFinite _
  haveI : Module.Finite (ZMod P.p)
      ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) :=
    Module.Finite.of_finite
  have hfr : Module.finrank (ZMod P.p)
      ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) =
      2 := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod P.p)
      (V := ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p))
    rw [ZMod.card] at h1
    have h2 : P.p ^ 2 = P.p ^ Module.finrank (ZMod P.p)
        ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) := by
      rw [← hcard, Nat.card_eq_fintype_card]
      exact h1
    exact Nat.pow_right_injective P.pp.two_le h2.symm
  by_cases hWL : W = L
  · -- the stable line IS the étale line: `χ₂` is unramified at `p`
    right
    intro σ hσ
    rw [MonoidHom.mem_ker]
    have hWtop : W ≠ ⊤ := by
      intro htop
      rw [htop, finrank_top, hfr] at hW1
      omega
    haveI : Nontrivial
        (((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) ⧸ W) :=
      Submodule.Quotient.nontrivial_iff.mpr hWtop
    obtain ⟨z, hz⟩ := exists_ne (0 :
      ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) ⧸ W)
    obtain ⟨v, rfl⟩ := W.mkQ_surjective z
    have h1 := hχ₂ ((Field.absoluteGaloisGroup.map (algebraMap ℚ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        P.pp.toHeightOneSpectrumRingOfIntegersRat))) σ) v
    have h2 := hL σ hσ v
    rw [← hWL] at h2
    rw [h2] at h1
    have h3 : ((1 : ZMod P.p) -
        (χ₂ ((Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            P.pp.toHeightOneSpectrumRingOfIntegersRat))) σ) : ZMod P.p)) •
        W.mkQ v = 0 := by
      rw [sub_smul, one_smul]
      exact sub_eq_zero_of_eq h1
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exact Units.ext (by
        rw [Units.val_one]
        exact (sub_eq_zero.mp h4).symm)
    · exact absurd h4 hz
  · -- the lines differ: `χ₁` is unramified at `p`
    left
    intro σ hσ
    rw [MonoidHom.mem_ker]
    have hW0 : W ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hW1
      omega
    haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW0
    obtain ⟨w₀, hw₀ne⟩ := exists_ne (0 : W)
    have hw₀V : (w₀ : ((P.freyCurve.map (algebraMap ℚ
        (AlgebraicClosure ℚ))).nTorsion P.p)) ≠ 0 :=
      fun hc => hw₀ne (Subtype.ext hc)
    -- `w₀ ∉ L`, else both lines are the span of `w₀`
    have hw₀L : (w₀ : ((P.freyCurve.map (algebraMap ℚ
        (AlgebraicClosure ℚ))).nTorsion P.p)) ∉ L := by
      intro hmem
      have hsp1 : Submodule.span (ZMod P.p) {(w₀ : ((P.freyCurve.map (algebraMap ℚ
          (AlgebraicClosure ℚ))).nTorsion P.p))} ≤ W := by
        rw [Submodule.span_le, Set.singleton_subset_iff]
        exact w₀.2
      have hsp2 : Submodule.span (ZMod P.p) {(w₀ : ((P.freyCurve.map (algebraMap ℚ
          (AlgebraicClosure ℚ))).nTorsion P.p))} ≤ L := by
        rw [Submodule.span_le, Set.singleton_subset_iff]
        exact hmem
      have hrk : Module.finrank (ZMod P.p)
          (Submodule.span (ZMod P.p) {(w₀ : ((P.freyCurve.map (algebraMap ℚ
            (AlgebraicClosure ℚ))).nTorsion P.p))}) = 1 :=
        finrank_span_singleton hw₀V
      have hWeq : Submodule.span (ZMod P.p) {(w₀ : ((P.freyCurve.map (algebraMap ℚ
          (AlgebraicClosure ℚ))).nTorsion P.p))} = W :=
        Submodule.eq_of_le_of_finrank_le hsp1 (le_of_eq (by rw [hW1, hrk]))
      have hLeq : Submodule.span (ZMod P.p) {(w₀ : ((P.freyCurve.map (algebraMap ℚ
          (AlgebraicClosure ℚ))).nTorsion P.p))} = L :=
        Submodule.eq_of_le_of_finrank_le hsp2 (le_of_eq (by rw [hL1, hrk]))
      exact hWL (hWeq.symm.trans hLeq)
    have hquotne : L.mkQ (w₀ : ((P.freyCurve.map (algebraMap ℚ
        (AlgebraicClosure ℚ))).nTorsion P.p)) ≠ 0 := by
      rw [Submodule.mkQ_apply, ne_eq, Submodule.Quotient.mk_eq_zero]
      exact hw₀L
    have h1 := hχ₁ ((Field.absoluteGaloisGroup.map (algebraMap ℚ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        P.pp.toHeightOneSpectrumRingOfIntegersRat))) σ)
      (w₀ : ((P.freyCurve.map (algebraMap ℚ
        (AlgebraicClosure ℚ))).nTorsion P.p)) w₀.2
    have h2 := hL σ hσ (w₀ : ((P.freyCurve.map (algebraMap ℚ
      (AlgebraicClosure ℚ))).nTorsion P.p))
    rw [h1, map_smul] at h2
    have h3 : ((1 : ZMod P.p) -
        (χ₁ ((Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            P.pp.toHeightOneSpectrumRingOfIntegersRat))) σ) : ZMod P.p)) •
        L.mkQ (w₀ : ((P.freyCurve.map (algebraMap ℚ
          (AlgebraicClosure ℚ))).nTorsion P.p)) = 0 := by
      rw [sub_smul, one_smul]
      exact sub_eq_zero_of_eq h2.symm
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exact Units.ext (by
        rw [Units.val_one]
        exact (sub_eq_zero.mp h4).symm)
    · exact absurd h4 hquotne

/-- **The flat/ordinary analysis at `p`** (DERIVED 2026-07-22 from the
two étale-line leaves and the PROVEN linear-algebra assembly): given
the stable line of the reducible mod-`p` Frey representation with its
characters `χ₁`, `χ₂` (multiplying to `ω̄`), one of the two is
unramified at `p` itself. The Frey curve is semistable at `p`
(`freyCurve_hasGoodReduction_of_not_dvd` /
`freyCurve_hasMultiplicativeReduction_of_dvd`, PROVEN, by `p ∣ abc` or
not); each reduction type yields an étale line via its leaf, and the
linear algebra compares it with the stable line. -/
theorem FreyPackage.subquotient_character_unramified_at_p
    (P : FreyPackage)
    (W : Submodule (ZMod P.p)
      ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p))
    (hW1 : Module.finrank (ZMod P.p) W = 1)
    (hstable : ∀ g v, v ∈ W → P.freyCurve.galoisRep P.p P.hppos g v ∈ W)
    (χ₁ χ₂ : Field.absoluteGaloisGroup ℚ →* (ZMod P.p)ˣ)
    (hχ₁ : ∀ g, ∀ v ∈ W,
      P.freyCurve.galoisRep P.p P.hppos g v = (χ₁ g : ZMod P.p) • v)
    (hχ₂ : ∀ g v, W.mkQ (P.freyCurve.galoisRep P.p P.hppos g v) =
      (χ₂ g : ZMod P.p) • W.mkQ v)
    (_hcyclo : ∀ g : Field.absoluteGaloisGroup ℚ,
      (χ₁ g : ZMod P.p) * (χ₂ g : ZMod P.p) =
        ((@GaloisRepresentation.cyclotomicCharacterModL P.p ⟨P.pp⟩ g :
          (ZMod P.p)ˣ) : ZMod P.p)) :
    (localInertiaGroup P.pp.toHeightOneSpectrumRingOfIntegersRat ≤
      (χ₁.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          P.pp.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker) ∨
    (localInertiaGroup P.pp.toHeightOneSpectrumRingOfIntegersRat ≤
      (χ₂.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          P.pp.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker) := by
  classical
  haveI : Fact P.p.Prime := ⟨P.pp⟩
  have hp2 : P.p ≠ 2 := by
    have := P.hp5
    omega
  by_cases hdvd : ((P.p : ℤ)) ∣ P.a * P.b * P.c
  · -- multiplicative reduction at `p`: the Tate étale line
    haveI := P.freyCurve_hasMultiplicativeReduction_of_dvd P.pp hp2 hdvd
    obtain ⟨L, hL1, hL⟩ :=
      WeierstrassCurve.exists_etale_line_of_multiplicative_self P.freyCurve P.pp
    exact P.character_unramified_at_p_of_etale_line W L hW1 hL1 χ₁ χ₂ hχ₁ hχ₂ hL
  · -- good reduction at `p`: the connected-étale line
    haveI := P.freyCurve_hasGoodReduction_of_not_dvd P.pp hp2 hdvd
    obtain ⟨L, hL1, hL⟩ :=
      WeierstrassCurve.exists_etale_line_of_good_of_stable_line P.freyCurve P.pp hp2
        W hW1 hstable
    exact P.character_unramified_at_p_of_etale_line W L hW1 hL1 χ₁ χ₂ hχ₁ hχ₂ hL

set_option backward.isDefEq.respectTransparency false in
/-- **The semistability-unramifiedness statement** (DERIVED 2026-07-17
from the two leaves above and the PROVEN machinery): given a stable
line in the mod-`p` torsion of the Frey curve with its sub- and
quotient-characters `χ₁`, `χ₂`, ONE of the two characters is unramified
at EVERY finite place. Assembly: away from `{2, p}` the whole
representation is unramified (`FreyCurve.torsion_isUnramified` — the
PROVEN Néron–Ogg–Shafarevich node at good primes, the Tate glue at
multiplicative ones), so both characters are trivial on inertia (the
unipotent-scalar lemmas at `(ρ(σ) − 1)² = 0`, which holds a fortiori
when `ρ(σ) = 1`); at `2` inertia is unipotent
(`inertia_two_unipotent`), so again both characters are unramified; at
`p` the flat/ordinary leaf selects one character, and that character is
then unramified everywhere. -/
theorem FreyPackage.subquotient_character_unramified
    (P : FreyPackage)
    (W : Submodule (ZMod P.p)
      ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p))
    (hW1 : Module.finrank (ZMod P.p) W = 1)
    (hstable : ∀ g v, v ∈ W → P.freyCurve.galoisRep P.p P.hppos g v ∈ W)
    (χ₁ χ₂ : Field.absoluteGaloisGroup ℚ →* (ZMod P.p)ˣ)
    (hχ₁ : ∀ g, ∀ v ∈ W,
      P.freyCurve.galoisRep P.p P.hppos g v = (χ₁ g : ZMod P.p) • v)
    (hχ₂ : ∀ g v, W.mkQ (P.freyCurve.galoisRep P.p P.hppos g v) =
      (χ₂ g : ZMod P.p) • W.mkQ v)
    (hcyclo : ∀ g : Field.absoluteGaloisGroup ℚ,
      (χ₁ g : ZMod P.p) * (χ₂ g : ZMod P.p) =
        ((@GaloisRepresentation.cyclotomicCharacterModL P.p ⟨P.pp⟩ g :
          (ZMod P.p)ˣ) : ZMod P.p)) :
    (∀ (q : ℕ) (hq : q.Prime),
      localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat ≤
        (χ₁.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker) ∨
    (∀ (q : ℕ) (hq : q.Prime),
      localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat ≤
        (χ₂.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker) := by
  classical
  haveI : Fact P.p.Prime := ⟨P.pp⟩
  -- rank bookkeeping: a nonzero vector of `W`, and `W ≠ ⊤`
  have hcard : Nat.card
      ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) =
      P.p ^ 2 :=
    TorsionCard.card_torsionBy
      (P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))) P.p
      (Nat.cast_ne_zero.mpr P.pp.ne_zero)
  haveI hfin : Finite
      ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) :=
    Nat.finite_of_card_ne_zero (by
      rw [hcard]
      have := P.pp.pos
      positivity)
  haveI : Fintype
      ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) :=
    Fintype.ofFinite _
  haveI : Module.Finite (ZMod P.p)
      ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) :=
    Module.Finite.of_finite
  have hfr : Module.finrank (ZMod P.p)
      ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) =
      2 := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod P.p)
      (V := ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p))
    rw [ZMod.card] at h1
    have h2 : P.p ^ 2 = P.p ^ Module.finrank (ZMod P.p)
        ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) := by
      rw [← hcard, Nat.card_eq_fintype_card]
      exact h1
    exact Nat.pow_right_injective P.pp.two_le h2.symm
  have hW0 : W ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hW1
    omega
  have hWtop : W ≠ ⊤ := by
    intro htop
    rw [htop, finrank_top, hfr] at hW1
    omega
  haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW0
  obtain ⟨w₀, hw₀ne⟩ := exists_ne (0 : W)
  have hw₀V : (w₀ : ((P.freyCurve.map (algebraMap ℚ
      (AlgebraicClosure ℚ))).nTorsion P.p)) ≠ 0 :=
    fun hc => hw₀ne (Subtype.ext hc)
  -- the characters are trivial at any unipotent inertia element
  have hgen₁ : ∀ (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers ℚ))
      (σ : Field.absoluteGaloisGroup
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)),
      ((P.freyCurve.galoisRep P.p P.hppos
          ((Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) σ) -
        1) ^ 2 = 0) →
      (χ₁.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          v))).toMonoidHom) σ = 1 := by
    intro v σ hsq
    apply Units.ext
    rw [Units.val_one, MonoidHom.comp_apply]
    exact subCharacter_eq_one_of_sq_eq_zero _ hsq hw₀V
      (hχ₁ _ (w₀ : ((P.freyCurve.map (algebraMap ℚ
        (AlgebraicClosure ℚ))).nTorsion P.p)) w₀.2)
  have hgen₂ : ∀ (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers ℚ))
      (σ : Field.absoluteGaloisGroup
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)),
      ((P.freyCurve.galoisRep P.p P.hppos
          ((Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) σ) -
        1) ^ 2 = 0) →
      (χ₂.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          v))).toMonoidHom) σ = 1 := by
    intro v σ hsq
    apply Units.ext
    rw [Units.val_one, MonoidHom.comp_apply]
    exact quotCharacter_eq_one_of_sq_eq_zero _ hsq W hWtop (hχ₂ _)
  -- triviality of the characters wherever the representation is trivial
  have htriv₁ : ∀ g, P.freyCurve.galoisRep P.p P.hppos g = 1 → χ₁ g = 1 := by
    intro g hg
    apply Units.ext
    rw [Units.val_one]
    refine subCharacter_eq_one_of_sq_eq_zero
      (P.freyCurve.galoisRep P.p P.hppos g) ?_ hw₀V
      (hχ₁ g (w₀ : ((P.freyCurve.map (algebraMap ℚ
        (AlgebraicClosure ℚ))).nTorsion P.p)) w₀.2)
    rw [hg, sub_self]
    exact zero_pow two_ne_zero
  have htriv₂ : ∀ g, P.freyCurve.galoisRep P.p P.hppos g = 1 → χ₂ g = 1 := by
    intro g hg
    apply Units.ext
    rw [Units.val_one]
    refine quotCharacter_eq_one_of_sq_eq_zero
      (P.freyCurve.galoisRep P.p P.hppos g) ?_ W hWtop (hχ₂ g)
    rw [hg, sub_self]
    exact zero_pow two_ne_zero
  -- assemble via the flat/ordinary leaf at `p`
  rcases P.subquotient_character_unramified_at_p W hW1 hstable χ₁ χ₂ hχ₁
    hχ₂ hcyclo with hp | hp
  · left
    intro q hq σ hσ
    by_cases hq2 : q = 2
    · subst hq2
      rw [MonoidHom.mem_ker]
      exact hgen₁ _ σ (P.inertia_two_unipotent σ hσ)
    · by_cases hqp : q = P.p
      · subst hqp
        exact hp hσ
      · have h4 := character_localInertia_le_ker_of_isUnramifiedAt
          (P.freyCurve.galoisRep P.p P.hppos)
          hq.toHeightOneSpectrumRingOfIntegersRat
          (FreyCurve.torsion_isUnramified P q hq ⟨hq2, hqp⟩) χ₁ htriv₁
        have h5 := h4 hσ
        convert h5 using 5
        exact Subsingleton.elim _ _
  · right
    intro q hq σ hσ
    by_cases hq2 : q = 2
    · subst hq2
      rw [MonoidHom.mem_ker]
      exact hgen₂ _ σ (P.inertia_two_unipotent σ hσ)
    · by_cases hqp : q = P.p
      · subst hqp
        exact hp hσ
      · have h4 := character_localInertia_le_ker_of_isUnramifiedAt
          (P.freyCurve.galoisRep P.p P.hppos)
          hq.toHeightOneSpectrumRingOfIntegersRat
          (FreyCurve.torsion_isUnramified P q hq ⟨hq2, hqp⟩) χ₂ htriv₂
        have h5 := h4 hσ
        convert h5 using 5
        exact Subsingleton.elim _ _

/-- **Serre's stable-line dichotomy for the Frey curve** (DERIVED
2026-07-17 from the semistability leaf and the PROVEN character
bookkeeping): if the mod-`p` representation of the Frey curve is not
irreducible, then (given the Minkowski input) either there is a
Galois-FIXED point of exact order `p` in `E(ℚ̄)`, or there is a stable
line `W` with the induced action on `E[p]/W` trivial. Assembly: the
stable line exists (`exists_stable_line_of_not_isIrreducible`), carries
characters `χ₁`, `χ₂` with `χ₁χ₂ = ω̄` (the DERIVED
`det_galoisRep_eq_cyclotomic` through the triangular determinant); the
semistability leaf makes one of them everywhere-unramified; its kernel
is open (it contains the open kernel of the representation); the
Minkowski hypothesis kills it; `χ₁ = 1` fixes a basis vector of `W`
pointwise, `χ₂ = 1` trivializes the quotient action. -/
theorem FreyPackage.stable_line_dichotomy_of_not_isIrreducible
    (P : FreyPackage)
    (hmink : ∀ χ : Field.absoluteGaloisGroup ℚ →* (ZMod P.p)ˣ,
      IsOpen (χ.ker : Set (Field.absoluteGaloisGroup ℚ)) →
      (∀ (q : ℕ) (hq : q.Prime),
        localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat ≤
          (χ.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker) →
      χ = 1)
    (h : ¬ (let E := P.freyCurve
            let p := P.p
            have : Fact p.Prime := ⟨P.pp⟩
            GaloisRep.IsIrreducible (E.galoisRep p P.hppos))) :
    (∃ Pt : ((P.freyCurve)⁄(AlgebraicClosure ℚ)).Point,
      addOrderOf Pt = P.p ∧
      ∀ σ : Field.absoluteGaloisGroup ℚ,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom Pt = Pt) ∨
    (∃ W : Submodule (ZMod P.p)
        ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p),
      W ≠ ⊥ ∧ W ≠ ⊤ ∧
      (∀ g : Field.absoluteGaloisGroup ℚ,
        ∀ v ∈ W, P.freyCurve.galoisRep P.p P.hppos g v ∈ W) ∧
      (∀ (g : Field.absoluteGaloisGroup ℚ)
        (v : (P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p),
        W.mkQ (P.freyCurve.galoisRep P.p P.hppos g v) = W.mkQ v)) := by
  classical
  haveI : Fact P.p.Prime := ⟨P.pp⟩
  -- the torsion space has rank `2`
  have hcard : Nat.card ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) = P.p ^ 2 :=
    TorsionCard.card_torsionBy
      (P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))) P.p
      (Nat.cast_ne_zero.mpr P.pp.ne_zero)
  haveI hfin : Finite ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    have := P.pp.pos
    positivity)
  haveI : Fintype ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) := Fintype.ofFinite _
  haveI : Module.Finite (ZMod P.p) ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) := Module.Finite.of_finite
  have hfr : Module.finrank (ZMod P.p) ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) = 2 := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod P.p) (V := ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p))
    rw [ZMod.card] at h1
    have h2 : P.p ^ 2 = P.p ^ Module.finrank (ZMod P.p) ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) := by
      rw [← hcard, Nat.card_eq_fintype_card]
      exact h1
    exact Nat.pow_right_injective P.pp.two_le h2.symm
  have hrank : Module.rank (ZMod P.p) ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) = 2 := by
    have h1 := Module.finrank_eq_rank (ZMod P.p) ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p)
    rw [hfr] at h1
    exact_mod_cast h1.symm
  -- the stable line
  have hirr : ¬ (P.freyCurve.galoisRep P.p P.hppos).IsIrreducible := h
  obtain ⟨W, hW1, hstable⟩ :=
    GaloisRepresentation.exists_stable_line_of_not_isIrreducible hrank (P.freyCurve.galoisRep P.p P.hppos) hirr
  have hW0 : W ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hW1
    omega
  have hWtop : W ≠ ⊤ := by
    intro htop
    rw [htop, finrank_top, hfr] at hW1
    omega
  have hQ1 : Module.finrank (ZMod P.p) (((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) ⧸ W) = 1 := by
    have hsum := Submodule.finrank_quotient_add_finrank W
    rw [hfr, hW1] at hsum
    omega
  -- the two characters
  obtain ⟨χ₁, hχ₁⟩ := exists_subCharacter (P.freyCurve.galoisRep P.p P.hppos) W hW1 hstable
  obtain ⟨χ₂, hχ₂⟩ := exists_quotCharacter (P.freyCurve.galoisRep P.p P.hppos) W hQ1 hstable
  -- `χ₁χ₂ = ω̄` through the determinant node
  have hcyclo : ∀ g, (χ₁ g : ZMod P.p) * (χ₂ g : ZMod P.p) =
      ((@GaloisRepresentation.cyclotomicCharacterModL P.p ⟨P.pp⟩ g :
        (ZMod P.p)ˣ) : ZMod P.p) := by
    intro g
    rw [← det_eq_subCharacter_mul_quotCharacter (P.freyCurve.galoisRep P.p P.hppos) W hW1 hQ1 hstable
      χ₁ χ₂ hχ₁ hχ₂ g, WeilPairing.cyclotomicCharacterModL_eq_toZMod]
    exact WeilPairing.det_galoisRep_eq_cyclotomic P.freyCurve P.p P.hppos
      (P.pp.odd_of_ne_two (by have := P.hp5; omega)) g
  -- the kernel of the representation is open …
  let Kρ : Subgroup (Field.absoluteGaloisGroup ℚ) :=
    { carrier := {g | (P.freyCurve.galoisRep P.p P.hppos) g = 1}
      one_mem' := map_one (P.freyCurve.galoisRep P.p P.hppos)
      mul_mem' := by
        intro a b ha hb
        show (P.freyCurve.galoisRep P.p P.hppos) (a * b) = 1
        rw [map_mul, ha, hb, mul_one]
      inv_mem' := by
        intro a ha
        show (P.freyCurve.galoisRep P.p P.hppos) a⁻¹ = 1
        have h1 : (P.freyCurve.galoisRep P.p P.hppos) a⁻¹ * (P.freyCurve.galoisRep P.p P.hppos) a = 1 := by
          rw [← map_mul, inv_mul_cancel, map_one]
        rwa [ha, mul_one] at h1 }
  have hKρ_open : IsOpen (Kρ : Set (Field.absoluteGaloisGroup ℚ)) :=
    isOpen_setOf_galoisRep_eq_one (P.freyCurve.galoisRep P.p P.hppos) hfin
  -- … and lies in the kernels of both characters
  have hnontrivW : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW0
  obtain ⟨w₀, hw₀ne⟩ := exists_ne (0 : W)
  have hw₀V : (w₀ : ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p)) ≠ 0 := fun hc => hw₀ne (Subtype.ext hc)
  have hker₁ : Kρ ≤ χ₁.ker := by
    intro g hg
    have hg1 : (P.freyCurve.galoisRep P.p P.hppos) g = 1 := hg
    rw [MonoidHom.mem_ker]
    have h1 := hχ₁ g (w₀ : ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p)) w₀.2
    rw [hg1, Module.End.one_apply] at h1
    have h2 : ((1 : ZMod P.p) - (χ₁ g : ZMod P.p)) • (w₀ : ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p)) = 0 := by
      rw [sub_smul, one_smul]
      exact sub_eq_zero_of_eq h1
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact Units.ext (by
        rw [Units.val_one]
        exact (sub_eq_zero.mp h3).symm)
    · exact absurd h3 hw₀V
  have hker₂ : Kρ ≤ χ₂.ker := by
    intro g hg
    have hg1 : (P.freyCurve.galoisRep P.p P.hppos) g = 1 := hg
    rw [MonoidHom.mem_ker]
    haveI : Nontrivial (((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) ⧸ W) :=
      Submodule.Quotient.nontrivial_iff.mpr hWtop
    obtain ⟨z, hz⟩ := exists_ne (0 : ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) ⧸ W)
    obtain ⟨v, rfl⟩ := W.mkQ_surjective z
    have h1 := hχ₂ g v
    rw [hg1, Module.End.one_apply] at h1
    have h2 : ((1 : ZMod P.p) - (χ₂ g : ZMod P.p)) • W.mkQ v = 0 := by
      rw [sub_smul, one_smul]
      exact sub_eq_zero_of_eq h1
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact Units.ext (by
        rw [Units.val_one]
        exact (sub_eq_zero.mp h3).symm)
    · exact absurd h3 hz
  have hopen₁ : IsOpen (χ₁.ker : Set (Field.absoluteGaloisGroup ℚ)) :=
    Subgroup.isOpen_mono hker₁ hKρ_open
  have hopen₂ : IsOpen (χ₂.ker : Set (Field.absoluteGaloisGroup ℚ)) :=
    Subgroup.isOpen_mono hker₂ hKρ_open
  -- the semistability leaf, then Minkowski
  rcases P.subquotient_character_unramified W hW1 hstable χ₁ χ₂ hχ₁ hχ₂
    hcyclo with hun₁ | hun₂
  · -- `χ₁ = 1`: the basis vector of `W` is a fixed point of order `p`
    have hχ₁triv : χ₁ = 1 := hmink χ₁ hopen₁ hun₁
    left
    refine ⟨(show ((P.freyCurve)⁄(AlgebraicClosure ℚ)).Point from
      (w₀ : ((P.freyCurve.map (algebraMap ℚ
        (AlgebraicClosure ℚ))).nTorsion P.p)).1), ?_, ?_⟩
    · -- exact order `p`
      have hsm : ((P.p : ℕ) : ℤ) •
          (w₀ : ((P.freyCurve.map (algebraMap ℚ
            (AlgebraicClosure ℚ))).nTorsion P.p)).1 = 0 :=
        (Submodule.mem_torsionBy_iff _ _).mp
          (w₀ : ((P.freyCurve.map (algebraMap ℚ
            (AlgebraicClosure ℚ))).nTorsion P.p)).2
      have hnat : P.p •
          (w₀ : ((P.freyCurve.map (algebraMap ℚ
            (AlgebraicClosure ℚ))).nTorsion P.p)).1 = 0 := by
        exact_mod_cast hsm
      have hdvd := addOrderOf_dvd_of_nsmul_eq_zero hnat
      have hne : (w₀ : ((P.freyCurve.map (algebraMap ℚ
          (AlgebraicClosure ℚ))).nTorsion P.p)).1 ≠ 0 :=
        fun hc => hw₀V (Subtype.ext hc)
      rcases P.pp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
      · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h1) hne
      · exact h1
    · -- fixed by every `σ`
      intro σ
      have h1 := hχ₁ σ (w₀ : ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p)) w₀.2
      rw [hχ₁triv] at h1
      simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h1
      exact congrArg Subtype.val h1
  · -- `χ₂ = 1`: the quotient action is trivial
    have hχ₂triv : χ₂ = 1 := hmink χ₂ hopen₂ hun₂
    right
    refine ⟨W, hW0, hWtop, fun g v hv => hstable g v hv, fun g v => ?_⟩
    have h1 := hχ₂ g v
    rw [hχ₂triv] at h1
    simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h1
    exact h1

section TwoTorsion

open WeierstrassCurve.Affine

/-- The trivial base change of the Frey curve to `ℚ` is elliptic. (Mathlib
has this instance for `E.map f`, but `WeierstrassCurve.baseChange` is a
non-reducible `def`, so instance search cannot see through it; several
derivations in this branch of the tree need the instance.) -/
instance (P : FreyPackage) : ((P.freyCurve)⁄ℚ).IsElliptic :=
  inferInstanceAs (P.freyCurve.map (algebraMap ℚ ℚ)).IsElliptic

/-- **Full rational 2-torsion of the Frey curve** (PROVEN 2026-07-16): the
Frey model has rational 2-torsion points `(0, 0)` and `(aᵖ/4, -aᵖ/8)` (in
the untransformed model `y² = x(x - aᵖ)(x + bᵖ)` the full 2-torsion is
visible; the transformed model retains it rationally, the quadratic
`x² + ((bᵖ-aᵖ)/4)x - aᵖbᵖ/16` factoring as `(x - aᵖ/4)(x + bᵖ/4)`). The
two points generate an injective `(ℤ/2)² →+ E(ℚ)`. -/
theorem FreyPackage.freyCurve_two_torsion_embedding (P : FreyPackage) :
    ∃ φ₂ : (ZMod 2 × ZMod 2) →+ ((P.freyCurve)⁄ℚ).Point, Function.Injective φ₂ := by
  -- the coefficients of the base-changed model
  have h1 : ((P.freyCurve)⁄ℚ).a₁ = 1 := by
    simp [WeierstrassCurve.baseChange, FreyPackage.freyCurve]
  have h2 : ((P.freyCurve)⁄ℚ).a₂ = (P.b ^ P.p - 1 - P.a ^ P.p) / 4 := by
    simp [WeierstrassCurve.baseChange, FreyPackage.freyCurve]
  have h3 : ((P.freyCurve)⁄ℚ).a₃ = 0 := by
    simp [WeierstrassCurve.baseChange, FreyPackage.freyCurve]
  have h4 : ((P.freyCurve)⁄ℚ).a₄ = -(P.a ^ P.p) * (P.b ^ P.p) / 16 := by
    simp [WeierstrassCurve.baseChange, FreyPackage.freyCurve]
  have h6 : ((P.freyCurve)⁄ℚ).a₆ = 0 := by
    simp [WeierstrassCurve.baseChange, FreyPackage.freyCurve]
  have hap : (P.a : ℚ) ^ P.p ≠ 0 := pow_ne_zero _ (by exact_mod_cast P.ha0)
  -- the two points satisfy the equation
  have heq₁ : ((P.freyCurve)⁄ℚ).Equation 0 0 := by
    rw [equation_iff, h1, h2, h3, h4, h6]
    ring
  have heq₂ : ((P.freyCurve)⁄ℚ).Equation
      ((P.a : ℚ) ^ P.p / 4) (-((P.a : ℚ) ^ P.p) / 8) := by
    rw [equation_iff, h1, h2, h3, h4, h6]
    field_simp
    ring
  have hns₁ : ((P.freyCurve)⁄ℚ).Nonsingular 0 0 :=
    equation_iff_nonsingular.mp heq₁
  have hns₂ : ((P.freyCurve)⁄ℚ).Nonsingular
      ((P.a : ℚ) ^ P.p / 4) (-((P.a : ℚ) ^ P.p) / 8) :=
    equation_iff_nonsingular.mp heq₂
  -- the points, their order-2 property, and their distinctness
  set Q₁ : ((P.freyCurve)⁄ℚ).Point := Point.some _ _ hns₁ with hQ₁def
  set Q₂ : ((P.freyCurve)⁄ℚ).Point := Point.some _ _ hns₂ with hQ₂def
  have hneg₁ : -Q₁ = Q₁ := by
    rw [hQ₁def, Point.neg_some]
    rw [Point.some.injEq]
    refine ⟨rfl, ?_⟩
    rw [negY, h1, h3]
    ring
  have hneg₂ : -Q₂ = Q₂ := by
    rw [hQ₂def, Point.neg_some]
    rw [Point.some.injEq]
    refine ⟨rfl, ?_⟩
    rw [negY, h1, h3]
    ring
  have h2Q₁ : (2 : ℤ) • Q₁ = 0 := by
    rw [two_zsmul]
    exact add_eq_zero_iff_eq_neg.mpr hneg₁.symm
  have h2Q₂ : (2 : ℤ) • Q₂ = 0 := by
    rw [two_zsmul]
    exact add_eq_zero_iff_eq_neg.mpr hneg₂.symm
  have hQ₁0 : Q₁ ≠ 0 := Point.some_ne_zero _
  have hQ₂0 : Q₂ ≠ 0 := Point.some_ne_zero _
  have hQ₁₂ : Q₁ ≠ Q₂ := by
    rw [hQ₁def, hQ₂def]
    intro h
    have hx := (Point.some.inj h).1
    rw [eq_comm, div_eq_iff (by norm_num : (4 : ℚ) ≠ 0), zero_mul] at hx
    exact hap hx
  -- assemble the embedding from the two order-2 points
  have hz₁ : (zmultiplesHom _ Q₁) (2 : ℤ) = 0 := h2Q₁
  have hz₂ : (zmultiplesHom _ Q₂) (2 : ℤ) = 0 := h2Q₂
  let f₁ : ZMod 2 →+ ((P.freyCurve)⁄ℚ).Point := ZMod.lift 2 ⟨zmultiplesHom _ Q₁, hz₁⟩
  let f₂ : ZMod 2 →+ ((P.freyCurve)⁄ℚ).Point := ZMod.lift 2 ⟨zmultiplesHom _ Q₂, hz₂⟩
  have hf₁ : f₁ 1 = Q₁ := by
    have := ZMod.lift_coe 2 (⟨zmultiplesHom _ Q₁, hz₁⟩ :
      {f : ℤ →+ ((P.freyCurve)⁄ℚ).Point // f 2 = 0}) (1 : ℤ)
    rw [show ((1 : ℤ) : ZMod 2) = 1 by norm_cast] at this
    rw [this]
    show (1 : ℤ) • Q₁ = Q₁
    rw [one_smul]
  have hf₂ : f₂ 1 = Q₂ := by
    have := ZMod.lift_coe 2 (⟨zmultiplesHom _ Q₂, hz₂⟩ :
      {f : ℤ →+ ((P.freyCurve)⁄ℚ).Point // f 2 = 0}) (1 : ℤ)
    rw [show ((1 : ℤ) : ZMod 2) = 1 by norm_cast] at this
    rw [this]
    show (1 : ℤ) • Q₂ = Q₂
    rw [one_smul]
  refine ⟨f₁.coprod f₂, (injective_iff_map_eq_zero _).mpr ?_⟩
  rintro ⟨i, j⟩ hx
  rw [AddMonoidHom.coprod_apply] at hx
  have hcases : ∀ i : ZMod 2, i = 0 ∨ i = 1 := by decide
  rcases hcases i with rfl | rfl <;> rcases hcases j with rfl | rfl
  · rfl
  · rw [map_zero, zero_add, hf₂] at hx
    exact absurd hx hQ₂0
  · rw [map_zero, add_zero, hf₁] at hx
    exact absurd hx hQ₁0
  · rw [hf₁, hf₂] at hx
    have h12 : Q₁ = Q₂ := by
      rw [eq_neg_of_add_eq_zero_left hx, hneg₂]
    exact absurd h12 hQ₁₂

end TwoTorsion

/-!
### The Vélu quotient (decomposed 2026-07-22; sharpened 2026-07-23)

`exists_quotient_curve_point` is DERIVED below from two leaves:

* `WeierstrassCurve.exists_quotient_isogeny` (DERIVED 2026-07-23 from
  the prime-order leaf below) — the quotient of an elliptic curve over
  `ℚ` by a finite Galois-stable subgroup of geometric points exists as
  an elliptic curve over `ℚ`, together with the Galois-equivariant
  quotient homomorphism on `ℚ̄`-points whose kernel is exactly the
  subgroup. The derivation is a strong induction on the cardinality of
  the subgroup: any nonzero stable `C` contains, for a prime
  `ℓ ∣ #C`, the stable subgroup `C₀ = C ⊓ E[ℓ]` (nonzero by Cauchy),
  which is either cyclic of order `ℓ` — quotient by the Vélu leaf — or
  all of `E[ℓ]` (`#E[ℓ] = ℓ²` forces the dichotomy by Lagrange) —
  quotient by multiplication by `ℓ`; the image of `C` in the quotient
  is stable of strictly smaller cardinality, and the composite of the
  two quotient maps has kernel exactly `C`.
* `WeierstrassCurve.exists_quotient_isogeny_of_prime_card` (DERIVED
  2026-07-23 from the two leaves below by the parity fork on `ℓ`; at
  `ℓ = 2` the unique nonzero element of `C` is Galois-fixed and
  descends to a rational `2`-torsion point).
* `WeierstrassCurve.exists_quotient_isogeny_of_rational_two_torsion`
  (DERIVED 2026-07-25 from the two bricks below) — the classical
  `2`-isogeny by a rational `2`-torsion point (Vélu 1971; Silverman
  AEC III.4.5, X.4.9). The derivation composes the normalising
  isomorphism with the normal-form isogeny.
  * `WeierstrassCurve.exists_normalForm_pointEquiv_of_rational_two_torsion`
    (PROVEN 2026-07-25) — the `ℚ`-isomorphism to `y² = x³ + a x² + b x`
    taking the `2`-torsion point to `(0, 0)`, packaged as a
    Galois-equivariant isomorphism on `ℚ̄`-points. A SINGLE admissible
    change of variables `(u, r, s, t) = (1, X, −a₁/2, Y)` does it: it
    kills `a₁` and `a₃` outright, kills `a₆` precisely because
    `T = (X, Y)` lies on `E`, and sends `(0, 0)` to `T`. Equivariance
    and the base change come from
    `Affine.Point.equivVariableChangeBaseChange(_galois)`.
  * `WeierstrassCurve.exists_quotient_isogeny_of_normalForm_two_torsion`
    (DERIVED 2026-07-25) — the explicit `2`-isogeny
    `(x, y) ↦ (y²/x², y (b − x²)/x²)` onto
    `y² = x³ − 2 a x² + (a² − 4 b) x`, with kernel `{0, (0, 0)}`. Built
    from `WeierstrassCurve.twoIsogenyFun` and its properties (see the
    section "The classical `2`-isogeny in normal form" below); all of
    them are PROVEN, the last of them being
    `WeierstrassCurve.twoIsogenyFun_add_of_ne` (the generic case of
    additivity, PROVEN 2026-07-25).
* `WeierstrassCurve.exists_quotient_isogeny_of_odd_prime_card`
  (DERIVED 2026-07-25) — the true Vélu core, the quotient by a
  Galois-stable subgroup of ODD order (primality is not used). Built
  in `Fermat/FLT/EllipticCurve/Velu.lean` from
  `WeierstrassCurve.exists_velu_quotient_isogeny`, where Vélu's map is
  written in group-law form; the Galois descent of the quotient
  curve's coefficients, the equivariance and the kernel are PROVEN
  there. **`velu_isElliptic`, `velu_equation` and `velu_map_add` are
  PROVEN** (as of 2026-07-26) and are NOT leaves — they are transitively
  sorried consumers, so do not dispatch at them. The actual leaves, all
  in `Velu.lean`, are `WeierstrassCurve.isElliptic_of_three_twoTorsion`,
  `WeierstrassCurve.velu_exists_three_twoTorsion`,
  `WeierstrassCurve.velu_pole_identity` and
  `WeierstrassCurve.velu_map_add_of_notMem` (Vélu 1971; Silverman AEC
  III.4.12).
* `FreyPackage.freyCurve_two_torsion_embedding` (PROVEN 2026-07-16,
  moved above this section) — the Frey curve's full rational
  `2`-torsion.

The assembly takes `C` to be the image of the line `W` (a cyclic
subgroup of order `p`, Galois-stable by `hstable`), pushes a vector
`v ∉ W` through the quotient map to get a Galois-fixed point of exact
order `p` (fixed because the quotient action is trivial, `hquot`),
pushes the rational `2`-torsion through (injectively, because the
kernel has odd exponent `p`), and descends both to `ℚ`-points by
`exists_point_eq_baseChange_of_fixed`.
-/

/-- **Normal form for a rational `2`-torsion point** (PROVEN, cut
2026-07-25 out of `exists_quotient_isogeny_of_rational_two_torsion`):
an elliptic curve over `ℚ` carrying a nonzero rational `2`-torsion
point `T` is `ℚ`-isomorphic to a curve in the normal form
`y² = x³ + a x² + b x` (that is, `⟨0, a, 0, b, 0⟩`) by an isomorphism
taking `T` to the point `(0, 0)`; the isomorphism induces a
Galois-equivariant isomorphism of the groups of `ℚ̄`-points.

Route (`char ℚ ≠ 2`): completing the square — the variable change
`(u, r, s, t) = (1, 0, -a₁/2, -a₃/2)` — brings `E` to the form
`y² = x³ + a₂' x² + a₄' x + a₆'`, in which the `2`-torsion points are
exactly the points `(x₀, 0)` with `x₀` a root of the cubic
(`2y + a₁x + a₃ = 0` characterises `2`-torsion, Silverman AEC III.2.3),
so `T` becomes `(x₀, 0)` with `x₀ ∈ ℚ`; the translation `x ↦ x + x₀`
— the variable change `(1, x₀, 0, 0)` — then moves `T` to `(0, 0)` and
makes the constant term vanish, leaving `y² = x³ + a x² + b x`. Both
changes are defined over `ℚ`, so the induced map on `ℚ̄`-points
(`Affine.Point.equivVariableChange` after base change) commutes with
the Galois action, its coordinate formulas having `ℚ`-coefficients.
Silverman AEC III.1, III.2.3. -/
theorem WeierstrassCurve.exists_normalForm_pointEquiv_of_rational_two_torsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (T : (E⁄ℚ).Point) (hT2 : T + T = 0) (hT0 : T ≠ 0) :
    ∃ (a b : ℚ) (_ : (⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ).IsElliptic)
      (h00 : ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).Nonsingular
        0 0)
      (Ψ : (E⁄(AlgebraicClosure ℚ)).Point ≃+
        ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).Point),
      (∀ (σ : Field.absoluteGaloisGroup ℚ) (Pt : (E⁄(AlgebraicClosure ℚ)).Point),
        Ψ (Affine.Point.map
            (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom Pt) =
          Affine.Point.map
            (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom (Ψ Pt)) ∧
      Ψ (Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) T) =
        Affine.Point.some 0 0 h00 := by
  -- Coordinates of the rational `2`-torsion point.
  rcases T with _ | ⟨X, Y, hns⟩
  · exact absurd rfl hT0
  have hY : 2 * Y + E.a₁ * X + E.a₃ = 0 := by
    by_contra hy
    have hy' : Y ≠ (E⁄ℚ).toAffine.negY X Y := by
      intro h
      have h2 : Y = -Y - E.a₁ * X - E.a₃ := h
      exact hy (by linarith [h2])
    exact Point.some_ne_zero _ ((Point.add_self_of_Y_ne hy').symm.trans hT2)
  have hEq : E.toAffine.Equation X Y := hns.1
  -- The normalising change of variables `(x, y) ↦ (x + X, y + (-a₁/2) x + Y)`; it takes
  -- `(0, 0)` to `T = (X, Y)`, kills `a₁` and `a₃`, and kills `a₆` because `T` is on `E`.
  set C : VariableChange ℚ := ⟨1, X, -E.a₁ / 2, Y⟩ with hC
  have h1 : (C • E).a₁ = 0 := by
    rw [variableChange_a₁, hC]; simp; ring
  have h3 : (C • E).a₃ = 0 := by
    rw [variableChange_a₃, hC]; simp; linarith [hY]
  have h6 : (C • E).a₆ = 0 := by
    rw [variableChange_a₆, hC]
    rw [Affine.equation_iff] at hEq
    simp
    linarith [hEq]
  obtain ⟨a, b, hWeq⟩ :
      ∃ a b : ℚ, C • E = (⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ) :=
    ⟨(C • E).a₂, (C • E).a₄, by ext <;> simp [h1, h3, h6]⟩
  -- `(0, 0)` is a nonsingular point of `C • E`, and of its base change.
  have h00Q' : (C • E).toAffine.Nonsingular 0 0 :=
    Affine.equation_iff_nonsingular.mp ((Affine.equation_zero (W := C • E)).mpr h6)
  have h00' : ((C • E)⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular 0 0 := by
    have := (Affine.baseChange_nonsingular (W := C • E) (A := ℚ) (B := AlgebraicClosure ℚ)
      (f := Algebra.ofId ℚ (AlgebraicClosure ℚ))
      (Algebra.ofId ℚ (AlgebraicClosure ℚ)).injective 0 0).mpr h00Q'
    simpa using this
  -- Transport of the point group along `C • E = E₀`, base changed to `ℚ̄`.
  have hbc : ((C • E)⁄(AlgebraicClosure ℚ)) =
      ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)) :=
    congrArg (fun V : WeierstrassCurve ℚ => V⁄(AlgebraicClosure ℚ)) hWeq
  have hOfEqGal : ∀ (V : WeierstrassCurve ℚ) (h : C • E = V)
      (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (P : ((C • E)⁄(AlgebraicClosure ℚ)).toAffine.Point),
      Point.equivOfEq (congrArg (fun V : WeierstrassCurve ℚ => V⁄(AlgebraicClosure ℚ)) h)
          (Point.map σ.toAlgHom P) =
        Point.map σ.toAlgHom
          (Point.equivOfEq
            (congrArg (fun V : WeierstrassCurve ℚ => V⁄(AlgebraicClosure ℚ)) h) P) := by
    rintro V rfl σ P
    rfl
  refine ⟨a, b, hWeq ▸ (inferInstance : (C • E).IsElliptic), hbc ▸ h00',
    (Point.equivVariableChangeBaseChange E C (AlgebraicClosure ℚ)).symm.trans
      (Point.equivOfEq hbc), ?_, ?_⟩
  · intro σ Pt
    have hsymm : (Point.equivVariableChangeBaseChange E C (AlgebraicClosure ℚ)).symm
          (Point.map (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom Pt) =
        Point.map (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom
          ((Point.equivVariableChangeBaseChange E C (AlgebraicClosure ℚ)).symm Pt) := by
      have hgal := Point.equivVariableChangeBaseChange_galois E C (AlgebraicClosure ℚ)
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        ((Point.equivVariableChangeBaseChange E C (AlgebraicClosure ℚ)).symm Pt)
      have hcong := congrArg
        (fun P => Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom P)
        ((Point.equivVariableChangeBaseChange E C (AlgebraicClosure ℚ)).apply_symm_apply Pt)
      exact (Point.equivVariableChangeBaseChange E C (AlgebraicClosure ℚ)).injective
        (((Point.equivVariableChangeBaseChange E C (AlgebraicClosure ℚ)).apply_symm_apply
            _).trans (hgal.trans hcong).symm)
    exact (congrArg (fun P => Point.equivOfEq hbc P) hsymm).trans (hOfEqGal _ hWeq _ _)
  · have he0 : Point.equivVariableChangeBaseChange E C (AlgebraicClosure ℚ)
          (Point.some 0 0 h00') =
        Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) (Point.some X Y hns) := by
      simp only [Point.equivVariableChangeBaseChange, AddEquiv.trans_apply, Point.equivOfEq_some,
        Point.equivVariableChange_some, Point.map_some]
      refine Point.some_eq_some (E⁄(AlgebraicClosure ℚ)) ?_ ?_ <;>
        simp [VariableChange.baseChange, VariableChange.map, hC]
    rw [AddEquiv.trans_apply, ← he0, AddEquiv.symm_apply_apply, Point.equivOfEq_some]

/-!
### The classical `2`-isogeny in normal form: explicit machinery (2026-07-25)

The bricks below build the explicit map
`φ(x, y) = (y²/x², y (b − x²)/x²)` from `y² = x³ + a x² + b x` to
`y² = x³ − 2 a x² + (a² − 4 b) x` and everything about it except the
generic case of its additivity.
-/

namespace WeierstrassCurve

/-- Discriminant of the two-torsion normal form `y² = x³ + a x² + b x`. -/
theorem normalForm_Δ (a b : ℚ) :
    (⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ).Δ = 16 * b ^ 2 * (a ^ 2 - 4 * b) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

theorem normalForm_a₄_ne_zero (a b : ℚ)
    [(⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ).IsElliptic] : b ≠ 0 := by
  intro hb
  have hΔ := (isUnit_Δ (W := (⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ))).ne_zero
  rw [normalForm_Δ, hb] at hΔ
  exact hΔ (by ring)

theorem normalForm_sq_sub_ne_zero (a b : ℚ)
    [(⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ).IsElliptic] : a ^ 2 - 4 * b ≠ 0 := by
  intro hb
  have hΔ := (isUnit_Δ (W := (⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ))).ne_zero
  rw [normalForm_Δ, hb] at hΔ
  exact hΔ (by ring)

/-- The codomain `y² = x³ − 2 a x² + (a² − 4 b) x` of the classical `2`-isogeny is again an
elliptic curve: its discriminant is `256 b (a² − 4 b)²`. -/
instance normalForm_codomain_isElliptic (a b : ℚ)
    [(⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ).IsElliptic] :
    (⟨0, -2 * a, 0, a ^ 2 - 4 * b, 0⟩ : WeierstrassCurve ℚ).IsElliptic := by
  refine ⟨?_⟩
  rw [show (⟨0, -2 * a, 0, a ^ 2 - 4 * b, 0⟩ : WeierstrassCurve ℚ).Δ
      = 16 * (a ^ 2 - 4 * b) ^ 2 * ((-2 * a) ^ 2 - 4 * (a ^ 2 - 4 * b)) from
    normalForm_Δ (-2 * a) (a ^ 2 - 4 * b)]
  refine isUnit_iff_ne_zero.mpr ?_
  have hb := normalForm_a₄_ne_zero a b
  have hd := normalForm_sq_sub_ne_zero a b
  intro hz
  rcases mul_eq_zero.mp hz with h1 | h2
  · rcases mul_eq_zero.mp h1 with h3 | h4
    · norm_num at h3
    · exact hd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h4)
  · exact hb (by linarith)

/-- The image of an affine point with `x ≠ 0` under the classical `2`-isogeny is a
nonsingular point of the codomain curve. -/
theorem twoIsogeny_nonsingular (a b : ℚ)
    [(⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ).IsElliptic]
    {x y : AlgebraicClosure ℚ}
    (heq : ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).Equation x y)
    (hx : x ≠ 0) :
    ((⟨0, -2 * a, 0, a ^ 2 - 4 * b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).Nonsingular
      (y ^ 2 / x ^ 2)
      (y * (algebraMap ℚ (AlgebraicClosure ℚ) b - x ^ 2) / x ^ 2) := by
  haveI : ((⟨0, -2 * a, 0, a ^ 2 - 4 * b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).IsElliptic
      := inferInstanceAs ((⟨0, -2 * a, 0, a ^ 2 - 4 * b, 0⟩ : WeierstrassCurve ℚ).map
      (algebraMap ℚ (AlgebraicClosure ℚ))).IsElliptic
  refine Affine.equation_iff_nonsingular.mp ?_
  set A := algebraMap ℚ (AlgebraicClosure ℚ) a with hA
  set B := algebraMap ℚ (AlgebraicClosure ℚ) b with hB
  rw [Affine.equation_iff] at heq ⊢
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map, map_zero, map_ofNat, map_mul,
    map_sub, map_pow, map_neg, ← hA, ← hB] at heq ⊢
  field_simp
  linear_combination (-(y ^ 2) * (y ^ 2 + x ^ 3 - A * x ^ 2 + B * x)) * heq

/-- The explicit classical `2`-isogeny on `ℚ̄`-points, `(x, y) ↦ (y²/x², y (b − x²)/x²)`,
with `0` and the `2`-torsion point `(0, 0)` sent to `0`. -/
noncomputable def twoIsogenyFun (a b : ℚ)
    [(⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ).IsElliptic] :
    ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).Point →
      ((⟨0, -2 * a, 0, a ^ 2 - 4 * b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).Point
  | .zero => 0
  | .some x _ hns =>
      if hx : x = 0 then 0
      else .some _ _ (twoIsogeny_nonsingular a b hns.1 hx)

@[simp] theorem twoIsogenyFun_zero (a b : ℚ)
    [(⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ).IsElliptic] :
    twoIsogenyFun a b 0 = 0 := rfl

theorem twoIsogenyFun_some_of_ne_zero (a b : ℚ)
    [(⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ).IsElliptic]
    {x y : AlgebraicClosure ℚ}
    (hns : ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).Nonsingular x y)
    (hx : x ≠ 0) :
    twoIsogenyFun a b (.some x y hns) =
      .some (y ^ 2 / x ^ 2) (y * (algebraMap ℚ (AlgebraicClosure ℚ) b - x ^ 2) / x ^ 2)
        (twoIsogeny_nonsingular a b hns.1 hx) := by
  rw [twoIsogenyFun, dif_neg hx]

theorem twoIsogenyFun_some_of_eq_zero (a b : ℚ)
    [(⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ).IsElliptic]
    {x y : AlgebraicClosure ℚ}
    (hns : ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).Nonsingular x y)
    (hx : x = 0) :
    twoIsogenyFun a b (.some x y hns) = 0 := by
  rw [twoIsogenyFun, dif_pos hx]

/-- An affine point of `y² = x³ + a x² + b x` with vanishing `x`-coordinate is `(0, 0)`. -/
theorem normalForm_y_eq_zero_of_x_eq_zero (a b : ℚ)
    {x y : AlgebraicClosure ℚ}
    (heq : ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).Equation x y)
    (hx : x = 0) : y = 0 := by
  rw [Affine.equation_iff] at heq
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map, map_zero, hx] at heq
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linear_combination heq)

/-- Galois equivariance of the explicit `2`-isogeny: its coordinate functions are rational
functions with `ℚ`-coefficients. -/
theorem twoIsogenyFun_map (a b : ℚ)
    [(⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ).IsElliptic]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (P : ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).Point) :
    twoIsogenyFun a b (Affine.Point.map σ.toAlgHom P) =
      Affine.Point.map σ.toAlgHom (twoIsogenyFun a b P) := by
  rcases P with _ | ⟨x, y, hns⟩
  · rfl
  · rcases eq_or_ne x 0 with hx | hx
    · rw [Point.map_some, twoIsogenyFun_some_of_eq_zero a b _ (by rw [hx]; exact map_zero _),
        twoIsogenyFun_some_of_eq_zero a b hns hx, map_zero]
    · have hσx : σ.toAlgHom x ≠ 0 := fun hc => hx (by simpa using congrArg σ.symm.toAlgHom hc)
      rw [Point.map_some, twoIsogenyFun_some_of_ne_zero a b _ hσx,
        twoIsogenyFun_some_of_ne_zero a b hns hx, Point.map_some]
      refine Point.some_eq_some _ ?_ ?_
      · simp [map_div₀]
      · simp [map_div₀]

/-- The kernel of the explicit `2`-isogeny is exactly `{0, (0, 0)}`. -/
theorem twoIsogenyFun_eq_zero_iff (a b : ℚ)
    [(⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ).IsElliptic]
    (h00 : ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).Nonsingular 0 0)
    (P : ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).Point) :
    twoIsogenyFun a b P = 0 ↔ P = 0 ∨ P = Affine.Point.some 0 0 h00 := by
  rcases P with _ | ⟨x, y, hns⟩
  · exact iff_of_true rfl (Or.inl rfl)
  · constructor
    · intro hP
      refine Or.inr ?_
      by_contra hne
      rcases eq_or_ne x 0 with hx | hx
      · exact hne (Point.some_eq_some _ hx (normalForm_y_eq_zero_of_x_eq_zero a b hns.1 hx))
      · rw [twoIsogenyFun_some_of_ne_zero a b hns hx] at hP
        exact Point.some_ne_zero _ hP
    · rintro (hc | hc)
      · exact absurd hc (Point.some_ne_zero _)
      · rw [twoIsogenyFun_some_of_eq_zero a b hns (Point.some.inj hc).1]

/-- Translation by the rational `2`-torsion point `(0, 0)`: for an affine point `(x, y)` of
`y² = x³ + a x² + b x` with `x ≠ 0`, one has `(0, 0) + (x, y) = (b/x, −b y/x²)`. -/
theorem normalForm_two_torsion_add (a b : ℚ)
    [(⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ).IsElliptic]
    {x y : AlgebraicClosure ℚ}
    (h₀ : ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).Nonsingular 0 0)
    (hns : ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).Nonsingular x y)
    (hx : x ≠ 0) :
    ∃ hns' : ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).Nonsingular
        (algebraMap ℚ (AlgebraicClosure ℚ) b / x)
        (-(algebraMap ℚ (AlgebraicClosure ℚ) b) * y / x ^ 2),
      (Affine.Point.some 0 0 h₀ + Affine.Point.some x y hns : _) =
        Affine.Point.some _ _ hns' := by
  set A := algebraMap ℚ (AlgebraicClosure ℚ) a with hA
  set B := algebraMap ℚ (AlgebraicClosure ℚ) b with hB
  have heq : y ^ 2 = x ^ 3 + A * x ^ 2 + B * x := by
    have := hns.1
    rw [Affine.equation_iff] at this
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map, map_zero, ← hA, ← hB] at this
    linear_combination this
  have hx0 : (0 : AlgebraicClosure ℚ) ≠ x := fun hc => hx hc.symm
  have hslope : ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).slope 0 x 0 y
      = y / x := by
    rw [Affine.slope_of_X_ne hx0]
    field_simp
    ring
  have hX : ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).addX 0 x
      (((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).slope 0 x 0 y) = B / x := by
    rw [hslope, Affine.addX]
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map, map_zero, ← hA, ← hB]
    field_simp
    linear_combination heq
  have hY : ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).addY 0 x 0
      (((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).slope 0 x 0 y)
      = -B * y / x ^ 2 := by
    rw [Affine.addY, Affine.negY, Affine.negAddY, hX, hslope]
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map, map_zero, ← hA, ← hB]
    field_simp
    ring
  rw [Point.add_of_X_ne hx0]
  exact ⟨hX ▸ hY ▸ Affine.nonsingular_add h₀ hns fun hxy => hx0 hxy.1,
    Point.some_eq_some _ hX hY⟩

/-- Additivity of the explicit `2`-isogeny in the degenerate case where one summand is the
kernel point `(0, 0)`: the isogeny kills `(0, 0)` and is invariant under translation by it. -/
theorem twoIsogenyFun_two_torsion_add (a b : ℚ)
    [(⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ).IsElliptic]
    (h₀ : ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).Nonsingular 0 0)
    {x y : AlgebraicClosure ℚ}
    (hns : ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).Nonsingular x y) :
    twoIsogenyFun a b (Affine.Point.some 0 0 h₀ + Affine.Point.some x y hns) =
      twoIsogenyFun a b (Affine.Point.some 0 0 h₀) +
        twoIsogenyFun a b (Affine.Point.some x y hns) := by
  have hB : algebraMap ℚ (AlgebraicClosure ℚ) b ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap ℚ (AlgebraicClosure ℚ)).injective).mpr
      (normalForm_a₄_ne_zero a b)
  rw [twoIsogenyFun_some_of_eq_zero a b h₀ rfl, zero_add]
  rcases eq_or_ne x 0 with hx | hx
  · have hy : y = 0 := normalForm_y_eq_zero_of_x_eq_zero a b hns.1 hx
    rw [twoIsogenyFun_some_of_eq_zero a b hns hx,
      Point.add_of_Y_eq (h₂ := hns) hx.symm
        (by rw [hy, Affine.negY]
            simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map, map_zero]
            ring),
      twoIsogenyFun_zero]
  · obtain ⟨hns', hsum⟩ := normalForm_two_torsion_add a b h₀ hns hx
    rw [hsum, twoIsogenyFun_some_of_ne_zero a b hns' (div_ne_zero hB hx),
      twoIsogenyFun_some_of_ne_zero a b hns hx]
    refine Point.some_eq_some _ ?_ ?_ <;> · field_simp <;> ring

/-- **The chord-and-tangent law from a line and Vieta** (PROVEN 2026-07-25): on a Weierstrass
curve in the form `y² = x³ + a₂ x² + a₄ x` (that is, `a₁ = a₃ = a₆ = 0`), suppose `L` and `M`
cut out a line meeting the curve in `(X₁, Y₁)`, `(X₂, Y₂)` and `(X₃, −Y₃)`, in the sense that
`Y₁ = L X₁ + M`, `Y₂ = L X₂ + M` and `Y₃ = −(L X₃ + M)`, and that the sum and product Vieta
relations `X₁ + X₂ + X₃ = L² − a₂` and `X₁X₂X₃ = M²` hold. Then the group law really does give
`(X₁, Y₁) + (X₂, Y₂) = (X₃, Y₃)`.

The point of the statement is that it is UNIFORM in the secant/tangent dichotomy: mathlib's
`slope` is defined by a case split on `X₁ = X₂`, and the two Vieta relations are exactly what
is needed to identify it with `L` in both branches. In the tangent branch `Y₁ ≠ negY X₂ Y₂`
forces `Y₁ = Y₂ ≠ 0`, hence `X₁ ≠ 0`; comparing the intersection cubic
`X³ + (a₂ − L²)X² + (a₄ − 2LM)X − M²`, which vanishes at `X₁`, with `(X−X₁)(X−X₂)(X−X₃)`,
whose `X²`- and constant coefficients agree with it by hypothesis, gives the remaining Vieta
relation `X₁X₂ + X₁X₃ + X₂X₃ = a₄ − 2LM`, and that is precisely the tangency condition
`2 Y₁ L = 3X₁² + 2a₂X₁ + a₄`. -/
theorem Affine.Point.add_eq_of_line {F : Type*} [Field F] [DecidableEq F]
    {W : WeierstrassCurve F} (h2 : (2 : F) ≠ 0)
    (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (ha₆ : W.a₆ = 0) {X₁ Y₁ X₂ Y₂ X₃ Y₃ L M : F}
    (h₁ : W.toAffine.Nonsingular X₁ Y₁) (h₂ : W.toAffine.Nonsingular X₂ Y₂)
    (h₃ : W.toAffine.Nonsingular X₃ Y₃)
    (hxy : ¬(X₁ = X₂ ∧ Y₁ = W.toAffine.negY X₂ Y₂))
    (hl₁ : Y₁ = L * X₁ + M) (hl₂ : Y₂ = L * X₂ + M)
    (hsum : X₁ + X₂ + X₃ = L ^ 2 - W.a₂)
    (hprod : X₁ * X₂ * X₃ = M ^ 2)
    (hY₃ : Y₃ = -(L * X₃ + M)) :
    Affine.Point.some X₁ Y₁ h₁ + Affine.Point.some X₂ Y₂ h₂ = Affine.Point.some X₃ Y₃ h₃ := by
  have hq₁ : Y₁ ^ 2 = X₁ ^ 3 + W.a₂ * X₁ ^ 2 + W.a₄ * X₁ := by
    have := h₁.1
    rw [Affine.equation_iff] at this
    rw [ha₁, ha₃, ha₆] at this
    linear_combination this
  have hslope : W.toAffine.slope X₁ X₂ Y₁ Y₂ = L := by
    by_cases hX : X₁ = X₂
    · have hY : Y₁ ≠ W.toAffine.negY X₂ Y₂ := fun h => hxy ⟨hX, h⟩
      have hnegY : W.toAffine.negY X₂ Y₂ = -Y₂ := by
        rw [Affine.negY, ha₁, ha₃]; ring
      have hY12 : Y₁ = Y₂ := Affine.Y_eq_of_Y_ne h₁.1 h₂.1 hX hY
      have hY0 : Y₁ ≠ 0 := by
        intro h
        exact hY (by rw [hnegY, ← hY12, h]; ring)
      have hX0 : X₁ ≠ 0 := by
        intro h
        exact hY0 (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
          (by rw [hq₁, h]; ring))
      have he₂ : X₁ * X₂ + X₁ * X₃ + X₂ * X₃ = W.a₄ - 2 * L * M := by
        have hz : (X₁ * X₂ + X₁ * X₃ + X₂ * X₃ - (W.a₄ - 2 * L * M)) * X₁ = 0 := by
          linear_combination hq₁ - (Y₁ + L * X₁ + M) * hl₁ + X₁ ^ 2 * hsum + hprod
        rcases mul_eq_zero.mp hz with h | h
        · linear_combination h
        · exact absurd h hX0
      have hnegY₁ : W.toAffine.negY X₁ Y₁ = -Y₁ := by
        rw [Affine.negY, ha₁, ha₃]; ring
      rw [Affine.slope_of_Y_ne hX hY, hnegY₁, ha₁]
      rw [div_eq_iff (by
        intro hc
        exact hY0 ((mul_eq_zero.mp (show (2 : F) * Y₁ = 0 by
          linear_combination hc)).resolve_left h2))]
      linear_combination (-2 * L) * hl₁ - he₂ + (2 * X₁) * hsum + (X₁ - X₃) * hX
    · rw [Affine.slope_of_X_ne hX, hl₁, hl₂]
      rw [div_eq_iff (sub_ne_zero.mpr hX)]
      ring
  rw [Point.add_some hxy]
  refine Point.some_eq_some W ?_ ?_
  · rw [Affine.addX, hslope, ha₁]; linear_combination -hsum
  · rw [Affine.addY, Affine.negY, Affine.negAddY, Affine.addX, hslope, ha₁, ha₃, hl₁, hY₃]
    linear_combination L * hsum

/-- The product Vieta relation `ν² = x₁x₂x₃` for the secant of `y² = x³ + A x² + B x` through
two points with distinct `x`-coordinates: with `d = x₁ − x₂`, `ℓ = (y₁−y₂)/d`, `ν = y₁ − ℓx₁`
and `x₃ = ℓ² − A − x₁ − x₂`, the certificate is `d x₂ · E₁ − d x₁ · E₂`. -/
theorem normalForm_nu_sq_of_X_ne {F : Type*} [Field F] (A B : F) {x₁ y₁ x₂ y₂ : F}
    (hd : x₁ - x₂ ≠ 0)
    (he₁ : y₁ ^ 2 = x₁ ^ 3 + A * x₁ ^ 2 + B * x₁)
    (he₂ : y₂ ^ 2 = x₂ ^ 3 + A * x₂ ^ 2 + B * x₂) :
    (y₁ - (y₁ - y₂) / (x₁ - x₂) * x₁) ^ 2
      = x₁ * x₂ * (((y₁ - y₂) / (x₁ - x₂)) ^ 2 - A - x₁ - x₂) := by
  field_simp [hd]
  linear_combination (-(x₁ - x₂) * x₂) * he₁ + ((x₁ - x₂) * x₁) * he₂

/-- The product Vieta relation `ν² = x₁²x₃` for the tangent of `y² = x³ + A x² + B x` at a
point with `y₁ ≠ 0`: with `ℓ = (3x₁²+2Ax₁+B)/(2y₁)` one has `ν = y₁ − ℓx₁ = x₁(B−x₁²)/(2y₁)`
and `x₃ = ℓ² − A − 2x₁ = ((B−x₁²)/(2y₁))²`; the certificate is `4y₁² · E₁`. -/
theorem normalForm_nu_sq_of_X_eq {F : Type*} [Field F] [CharZero F] (A B : F) {x₁ y₁ : F}
    (hy : y₁ ≠ 0) (he₁ : y₁ ^ 2 = x₁ ^ 3 + A * x₁ ^ 2 + B * x₁) :
    (y₁ - (3 * x₁ ^ 2 + 2 * A * x₁ + B) / (2 * y₁) * x₁) ^ 2
      = x₁ * x₁ * (((3 * x₁ ^ 2 + 2 * A * x₁ + B) / (2 * y₁)) ^ 2 - A - x₁ - x₁) := by
  field_simp
  linear_combination (4 * y₁ ^ 2) * he₁

/-- The image of a point of `y² = x³ + A x² + B x` under `φ(x,y) = (y²/x², y(B−x²)/x²)` lies on
the line of the codomain curve with slope `Λ = (B − ℓν)/ν` and intercept
`M = (Aℓν − Bℓ² − ν²)/ν`, whenever the point lies on the domain line `y = ℓx + ν` and
`ν ≠ 0`. The certificate is `ℓν·E − (By + νx² + Bℓx)·(y − ℓx − ν)`. -/
theorem normalForm_twoIsogeny_line {F : Type*} [Field F] (A B : F) {x y L ν : F}
    (hx : x ≠ 0) (hν : ν ≠ 0)
    (hcx : y ^ 2 = x ^ 3 + A * x ^ 2 + B * x) (hlx : y = L * x + ν) :
    y * (B - x ^ 2) / x ^ 2
      = (B - L * ν) / ν * (y ^ 2 / x ^ 2) + (A * L * ν - B * L ^ 2 - ν ^ 2) / ν := by
  field_simp
  linear_combination (L * ν) * hcx - (B * y + ν * x ^ 2 + B * L * x) * hlx

/-- The sum Vieta relation on the codomain: `X₁ + X₂ + X₃ = Λ² + 2A` for `X_i = y_i²/x_i²`.
Each `X_i = x_i + A + B/x_i`, so the claim reduces to the three domain Vieta relations. -/
theorem normalForm_twoIsogeny_xSum {F : Type*} [Field F] (A B : F) {x₁ y₁ x₂ y₂ x₃ y₃ L ν : F}
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0) (hx₃ : x₃ ≠ 0) (hν : ν ≠ 0)
    (he₁ : y₁ ^ 2 = x₁ ^ 3 + A * x₁ ^ 2 + B * x₁)
    (he₂ : y₂ ^ 2 = x₂ ^ 3 + A * x₂ ^ 2 + B * x₂)
    (he₃ : y₃ ^ 2 = x₃ ^ 3 + A * x₃ ^ 2 + B * x₃)
    (hV1 : x₁ + x₂ + x₃ = L ^ 2 - A)
    (hV2 : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = B - 2 * L * ν)
    (hV3 : ν ^ 2 = x₁ * x₂ * x₃) :
    y₁ ^ 2 / x₁ ^ 2 + y₂ ^ 2 / x₂ ^ 2 + y₃ ^ 2 / x₃ ^ 2 = ((B - L * ν) / ν) ^ 2 + 2 * A := by
  have hXi : ∀ {x y : F}, x ≠ 0 → y ^ 2 = x ^ 3 + A * x ^ 2 + B * x →
      y ^ 2 / x ^ 2 = x + A + B / x := by
    intro x y hx hcx
    field_simp
    linear_combination hcx
  rw [hXi hx₁ he₁, hXi hx₂ he₂, hXi hx₃ he₃]
  field_simp
  linear_combination (x₁ * x₂ * x₃ * ν ^ 2) * hV1 + (B * ν ^ 2) * hV2 -
    (L ^ 2 * ν ^ 2 - (B - L * ν) ^ 2) * hV3

/-- The product Vieta relation on the codomain: `X₁X₂X₃ = M²` for `X_i = y_i²/x_i²`. It comes
from `y₁y₂y₃ = ν(Aℓν − Bℓ² − ν²) = νM` together with `x₁x₂x₃ = ν²`. -/
theorem normalForm_twoIsogeny_xProd {F : Type*} [Field F] (A B : F) {x₁ y₁ x₂ y₂ x₃ y₃ L ν : F}
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0) (hx₃ : x₃ ≠ 0) (hν : ν ≠ 0)
    (hl₁ : y₁ = L * x₁ + ν) (hl₂ : y₂ = L * x₂ + ν) (hl₃ : y₃ = -(L * x₃ + ν))
    (hV1 : x₁ + x₂ + x₃ = L ^ 2 - A)
    (hV2 : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = B - 2 * L * ν)
    (hV3 : ν ^ 2 = x₁ * x₂ * x₃) :
    y₁ ^ 2 / x₁ ^ 2 * (y₂ ^ 2 / x₂ ^ 2) * (y₃ ^ 2 / x₃ ^ 2)
      = ((A * L * ν - B * L ^ 2 - ν ^ 2) / ν) ^ 2 := by
  have hprodY : y₁ * y₂ * y₃ = ν * (A * L * ν - B * L ^ 2 - ν ^ 2) := by
    linear_combination y₂ * y₃ * hl₁ + (L * x₁ + ν) * y₃ * hl₂ +
      (L * x₁ + ν) * (L * x₂ + ν) * hl₃ + L ^ 3 * hV3 - L ^ 2 * ν * hV2 - L * ν ^ 2 * hV1
  have h1 : y₁ ^ 2 / x₁ ^ 2 * (y₂ ^ 2 / x₂ ^ 2) * (y₃ ^ 2 / x₃ ^ 2)
      = (y₁ * y₂ * y₃) ^ 2 / (x₁ * x₂ * x₃) ^ 2 := by
    field_simp
  rw [h1, ← hV3, hprodY, div_pow,
    div_eq_div_iff (pow_ne_zero 2 (pow_ne_zero 2 hν)) (pow_ne_zero 2 hν)]
  ring

/-- **The generic case of the additivity of the explicit `2`-isogeny** (PROVEN 2026-07-25;
cut out of `WeierstrassCurve.twoIsogenyFun_add`, whose degenerate cases — a zero summand, a
summand equal to the kernel point `(0, 0)`, and `P + Q = 0` — are proven there): for two
affine points of `y² = x³ + a x² + b x` with nonzero `x`-coordinates whose sum is not `0`,
the explicit map `φ(x, y) = (y²/x², y (b − x²)/x²)` is additive.

Route (all of it pure coordinate algebra over `ℚ̄`; write `A = a`, `B = b` in `ℚ̄`). Let `ℓ`
be mathlib's `slope x₁ x₂ y₁ y₂`, `ν = y₁ − ℓ x₁` the intercept of the line through the two
points, and `(x₃, y₃) = P + Q`, so that `x₃ = ℓ² − A − x₁ − x₂` and `y₃ = −(ℓ x₃ + ν)`.

* `y₂ = ℓ x₂ + ν` and the product Vieta relation `ν² = x₁x₂x₃` are the ONLY two facts needing
  the secant/tangent case split. In the secant branch the certificate is
  `x₁x₂((y₁−y₂)² − (A+x₁+x₂)d²) − (x₁y₂−x₂y₁)² = d x₂·E₁ − d x₁·E₂` with `d = x₁ − x₂`; in
  the tangent branch `ℓ = (3x₁²+2Ax₁+B)/(2y₁)`, `ν = x₁(B−x₁²)/(2y₁)` and the certificate is
  `4y₁²·E₁`.
* Everything downstream is uniform. The remaining Vieta relation
  `x₁x₂ + x₁x₃ + x₂x₃ = B − 2ℓν` follows from `E₁`, the sum and product relations and
  `x₁ ≠ 0`, by evaluating the intersection cubic at `x₁`; and `(x₃, y₃)` satisfies the curve
  equation for the same reason.
* `x₃ = 0 ↔ ν = 0`, and in that branch `x₁x₂ = B`, so `X₁ = ℓ² = X₂` and `Y₁ + Y₂ = 0`: both
  sides are `0`, which is exactly "`φP + φQ = 0` iff `P + Q ∈ ker φ`".
* In the branch `ν ≠ 0` the images lie on the line of the codomain curve with slope and
  intercept `Λ = (B − ℓν)/ν` and `M = (Aℓν − Bℓ² − ν²)/ν`. Writing `s_i = y_i/x_i = ℓ + ν/x_i`
  one has `X_i = s_i²`, `Y_i = s_i(s_i² − 2x_i − A)`, `Λ = s₁+s₂+s₃−2ℓ` and `M = −s₁s₂s₃`;
  concretely `y₁y₂y₃ = ν(Aℓν − Bℓ² − ν²)` gives `X₁X₂X₃ = M²`, and `X_i = x_i + A + B/x_i`
  gives `X₁+X₂+X₃ = Λ² + 2A`. `Affine.Point.add_eq_of_line` then closes it uniformly.
* Finally the images are not opposite: `Y₁ = −Y₂` together with the line forces `Y₁ = Y₂ = 0`;
  if `X₁ = 0` then `y₁ = y₂ = 0` and either `ℓ = 0` (so `ν = 0`) or `x₁ = x₂` (contradicting
  the hypothesis), while if `X₁ ≠ 0` then `M = −ΛX₁`, so `X₃ = Λ²` by the product relation and
  `X₁ = A` by the sum relation, whence the codomain equation gives `4AB = 0` and `A = X₁ = 0`.

Silverman AEC III.4.5, X.4.9 and Exercise 3.13; Washington, *Elliptic Curves*, ch. 8. -/
theorem twoIsogenyFun_add_of_ne (a b : ℚ)
    [(⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ).IsElliptic]
    {x₁ y₁ x₂ y₂ : AlgebraicClosure ℚ}
    (h₁ : ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).Nonsingular x₁ y₁)
    (h₂ : ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).Nonsingular x₂ y₂)
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (hxy : ¬(x₁ = x₂ ∧
      y₁ = ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).negY x₂ y₂)) :
    twoIsogenyFun a b (Affine.Point.some x₁ y₁ h₁ + Affine.Point.some x₂ y₂ h₂) =
      twoIsogenyFun a b (Affine.Point.some x₁ y₁ h₁) +
        twoIsogenyFun a b (Affine.Point.some x₂ y₂ h₂) := by
  set A := algebraMap ℚ (AlgebraicClosure ℚ) a with hA
  set B := algebraMap ℚ (AlgebraicClosure ℚ) b with hB
  have hB0 : B ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap ℚ (AlgebraicClosure ℚ)).injective).mpr
      (normalForm_a₄_ne_zero a b)
  -- the affine equation of the domain curve, in cleared form
  have hcurve : ∀ {x y : AlgebraicClosure ℚ},
      ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).Equation x y →
        y ^ 2 = x ^ 3 + A * x ^ 2 + B * x := by
    intro x y h
    rw [Affine.equation_iff] at h
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map, map_zero, ← hA, ← hB] at h
    linear_combination h
  have he₁ : y₁ ^ 2 = x₁ ^ 3 + A * x₁ ^ 2 + B * x₁ := hcurve h₁.1
  have he₂ : y₂ ^ 2 = x₂ ^ 3 + A * x₂ ^ 2 + B * x₂ := hcurve h₂.1
  -- the negation on the domain and codomain curves
  have hnegY : ∀ x y : AlgebraicClosure ℚ,
      ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).negY x y = -y := by
    intro x y
    rw [Affine.negY]
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map, map_zero]
    ring
  have hnegY' : ∀ X Y : AlgebraicClosure ℚ,
      ((⟨0, -2 * a, 0, a ^ 2 - 4 * b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).negY X Y
        = -Y := by
    intro X Y
    rw [Affine.negY]
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map, map_zero]
    ring
  -- the line through the two points
  set L := ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).slope x₁ x₂ y₁ y₂
    with hLdef
  set ν := y₁ - L * x₁ with hνdef
  have hl₁ : y₁ = L * x₁ + ν := by rw [hνdef]; ring
  have hl₂ : y₂ = L * x₂ + ν := by
    by_cases hx : x₁ = x₂
    · have hy : y₁ = y₂ := Affine.Y_eq_of_Y_ne h₁.1 h₂.1 hx (fun h => hxy ⟨hx, h⟩)
      rw [← hy, ← hx]; exact hl₁
    · have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
      rw [hνdef, hLdef, Affine.slope_of_X_ne hx]
      field_simp [hd]
      ring
  set x₃ := L ^ 2 - A - x₁ - x₂ with hx₃def
  set y₃ := -(L * x₃ + ν) with hy₃def
  -- Vieta: the product of the three roots of the intersection cubic
  have hV3 : ν ^ 2 = x₁ * x₂ * x₃ := by
    by_cases hx : x₁ = x₂
    · have hy : y₁ = y₂ := Affine.Y_eq_of_Y_ne h₁.1 h₂.1 hx (fun h => hxy ⟨hx, h⟩)
      have hy0 : y₁ ≠ 0 := by
        intro h
        exact hxy ⟨hx, by rw [hnegY, h, ← hy, h, neg_zero]⟩
      have hL : L = (3 * x₁ ^ 2 + 2 * A * x₁ + B) / (2 * y₁) := by
        rw [hLdef, Affine.slope_of_Y_ne hx (fun h => hxy ⟨hx, h⟩), hnegY]
        simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map, map_zero, ← hA, ← hB]
        rw [div_eq_div_iff (by
            intro hc
            exact hy0 ((mul_eq_zero.mp (show (2 : AlgebraicClosure ℚ) * y₁ = 0 by
              linear_combination hc)).resolve_left two_ne_zero))
          (by
            intro hc
            exact hy0 ((mul_eq_zero.mp (show (2 : AlgebraicClosure ℚ) * y₁ = 0 by
              linear_combination hc)).resolve_left two_ne_zero))]
        ring
      rw [hx₃def, hνdef, hL, ← hx]
      exact normalForm_nu_sq_of_X_eq A B hy0 he₁
    · have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
      rw [hx₃def, hνdef, hLdef, Affine.slope_of_X_ne hx]
      exact normalForm_nu_sq_of_X_ne A B hd he₁ he₂
  have hV1 : x₁ + x₂ + x₃ = L ^ 2 - A := by rw [hx₃def]; ring
  have haddX : ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).addX x₁ x₂ L
      = x₃ := by
    rw [Affine.addX]
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map, map_zero, ← hA]
    rw [hx₃def]; ring
  have haddY : ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).addY x₁ x₂ y₁ L
      = y₃ := by
    rw [Affine.addY, Affine.negAddY, hnegY, Affine.addX]
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map, map_zero, ← hA]
    rw [hy₃def, hx₃def, hνdef]; ring
  have hl₃ : y₃ = -(L * x₃ + ν) := hy₃def
  have hns₃ : ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).Nonsingular x₃ y₃ :=
    haddX ▸ haddY ▸ Affine.nonsingular_add h₁ h₂ hxy
  rw [Point.add_some hxy,
    Point.some_eq_some ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ))
      haddX haddY (h₂ := hns₃),
    twoIsogenyFun_some_of_ne_zero a b h₁ hx₁, twoIsogenyFun_some_of_ne_zero a b h₂ hx₂]
  -- from here on the four quantities are opaque, so that `ring` stays small
  clear_value y₃ x₃ ν L
  have hV2 : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = B - 2 * L * ν := by
    have hz : (x₁ * x₂ + x₁ * x₃ + x₂ * x₃ - (B - 2 * L * ν)) * x₁ = 0 := by
      linear_combination he₁ - (y₁ + L * x₁ + ν) * hl₁ + x₁ ^ 2 * hV1 - hV3
    rcases mul_eq_zero.mp hz with h | h
    · linear_combination h
    · exact absurd h hx₁
  have he₃ : y₃ ^ 2 = x₃ ^ 3 + A * x₃ ^ 2 + B * x₃ := by
    linear_combination (y₃ - L * x₃ - ν) * hl₃ - x₃ ^ 2 * hV1 + x₃ * hV2 + hV3
  by_cases hx₃0 : x₃ = 0
  · -- `P + Q` lies in the kernel of the isogeny; both sides are `0`
    rw [twoIsogenyFun_some_of_eq_zero a b hns₃ hx₃0]
    have hν0 : ν = 0 := by
      have h : ν ^ 2 = 0 := by rw [hV3, hx₃0]; ring
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    have hxx : x₁ * x₂ = B := by
      rw [hx₃0, hν0] at hV2
      linear_combination hV2
    refine (Point.add_of_Y_eq ?_ ?_).symm
    · rw [hl₁, hl₂, hν0]
      field_simp
      ring
    · rw [hnegY', hl₁, hl₂, hν0]
      field_simp
      linear_combination (-(L * x₁ * x₂ * (x₁ + x₂))) * hxx
  · -- the generic branch: the images span a genuine secant or tangent line
    rw [twoIsogenyFun_some_of_ne_zero a b hns₃ hx₃0]
    have hν0 : ν ≠ 0 := by
      intro h
      refine hx₃0 ?_
      have h' : (0 : AlgebraicClosure ℚ) = x₁ * x₂ * x₃ := by rw [← hV3, h]; ring
      exact ((mul_eq_zero.mp h'.symm).resolve_left (mul_ne_zero hx₁ hx₂))
    set Λ := (B - L * ν) / ν with hΛdef
    set M := (A * L * ν - B * L ^ 2 - ν ^ 2) / ν with hMdef
    clear_value Λ M
    have hl₁' : y₁ * (B - x₁ ^ 2) / x₁ ^ 2 = Λ * (y₁ ^ 2 / x₁ ^ 2) + M := by
      rw [hΛdef, hMdef]; exact normalForm_twoIsogeny_line A B hx₁ hν0 he₁ hl₁
    have hl₂' : y₂ * (B - x₂ ^ 2) / x₂ ^ 2 = Λ * (y₂ ^ 2 / x₂ ^ 2) + M := by
      rw [hΛdef, hMdef]; exact normalForm_twoIsogeny_line A B hx₂ hν0 he₂ hl₂
    have hl₃' : y₃ * (B - x₃ ^ 2) / x₃ ^ 2 = -(Λ * (y₃ ^ 2 / x₃ ^ 2) + M) := by
      have h := normalForm_twoIsogeny_line A B hx₃0 hν0
        (show (-y₃) ^ 2 = x₃ ^ 3 + A * x₃ ^ 2 + B * x₃ by linear_combination he₃)
        (show -y₃ = L * x₃ + ν by linear_combination -hl₃)
      rw [hΛdef, hMdef]
      linear_combination -h
    have hsum' : y₁ ^ 2 / x₁ ^ 2 + y₂ ^ 2 / x₂ ^ 2 + y₃ ^ 2 / x₃ ^ 2 = Λ ^ 2 + 2 * A := by
      rw [hΛdef]
      exact normalForm_twoIsogeny_xSum A B hx₁ hx₂ hx₃0 hν0 he₁ he₂ he₃ hV1 hV2 hV3
    have hprod' : y₁ ^ 2 / x₁ ^ 2 * (y₂ ^ 2 / x₂ ^ 2) * (y₃ ^ 2 / x₃ ^ 2) = M ^ 2 := by
      rw [hMdef]
      exact normalForm_twoIsogeny_xProd A B hx₁ hx₂ hx₃0 hν0 hl₁ hl₂ hl₃ hV1 hV2 hV3
    -- the two image points are not opposite, so the codomain sum is not `0`
    have hxy' : ¬(y₁ ^ 2 / x₁ ^ 2 = y₂ ^ 2 / x₂ ^ 2 ∧
        y₁ * (B - x₁ ^ 2) / x₁ ^ 2 =
          ((⟨0, -2 * a, 0, a ^ 2 - 4 * b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).negY
            (y₂ ^ 2 / x₂ ^ 2) (y₂ * (B - x₂ ^ 2) / x₂ ^ 2)) := by
      rintro ⟨hXe, hYe⟩
      rw [hnegY'] at hYe
      have hY12 : y₁ * (B - x₁ ^ 2) / x₁ ^ 2 = y₂ * (B - x₂ ^ 2) / x₂ ^ 2 := by
        rw [hl₁', hl₂', hXe]
      have hY10 : y₁ * (B - x₁ ^ 2) / x₁ ^ 2 = 0 :=
        ((mul_eq_zero.mp (show (2 : AlgebraicClosure ℚ) * (y₁ * (B - x₁ ^ 2) / x₁ ^ 2) = 0 by
          linear_combination hYe + hY12)).resolve_left two_ne_zero)
      have hM' : M = -(Λ * (y₁ ^ 2 / x₁ ^ 2)) := by linear_combination hY10 - hl₁'
      by_cases hX10 : y₁ ^ 2 / x₁ ^ 2 = 0
      · have hy₁0 : y₁ = 0 :=
          pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
            ((div_eq_zero_iff.mp hX10).resolve_right (pow_ne_zero 2 hx₁))
        have hy₂0 : y₂ = 0 :=
          pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
            ((div_eq_zero_iff.mp (hXe ▸ hX10 : y₂ ^ 2 / x₂ ^ 2 = 0)).resolve_right
              (pow_ne_zero 2 hx₂))
        have hLx : L * (x₁ - x₂) = 0 := by
          linear_combination -hl₁ + hl₂ + hy₁0 - hy₂0
        rcases mul_eq_zero.mp hLx with hL0 | hx12
        · exact hν0 (by linear_combination -hl₁ + hy₁0 - x₁ * hL0)
        · exact hxy ⟨sub_eq_zero.mp hx12, by rw [hnegY, hy₁0, hy₂0, neg_zero]⟩
      · have hX3 : y₃ ^ 2 / x₃ ^ 2 = Λ ^ 2 := by
          have hz : (y₁ ^ 2 / x₁ ^ 2) ^ 2 * (y₃ ^ 2 / x₃ ^ 2 - Λ ^ 2) = 0 := by
            linear_combination hprod' + y₁ ^ 2 / x₁ ^ 2 * (y₃ ^ 2 / x₃ ^ 2) * hXe +
              (M - Λ * (y₁ ^ 2 / x₁ ^ 2)) * hM'
          rcases mul_eq_zero.mp hz with h | h
          · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h) hX10
          · linear_combination h
        have hXA : y₁ ^ 2 / x₁ ^ 2 = A := by
          have hz : (2 : AlgebraicClosure ℚ) * (y₁ ^ 2 / x₁ ^ 2 - A) = 0 := by
            linear_combination hsum' + hXe - hX3
          linear_combination (mul_eq_zero.mp hz).resolve_left two_ne_zero
        have hq : (y₁ * (B - x₁ ^ 2) / x₁ ^ 2) ^ 2 = (y₁ ^ 2 / x₁ ^ 2) ^ 3 +
            (-2 * A) * (y₁ ^ 2 / x₁ ^ 2) ^ 2 + (A ^ 2 - 4 * B) * (y₁ ^ 2 / x₁ ^ 2) := by
          have h := (twoIsogeny_nonsingular a b h₁.1 hx₁).1
          rw [Affine.equation_iff] at h
          simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map, map_zero, map_mul,
            map_sub, map_pow, map_neg, map_ofNat, ← hA, ← hB] at h
          linear_combination h
        rw [hY10, hXA] at hq
        have hAB : A * B = 0 := by linear_combination hq / 4
        exact hX10 (by rw [hXA, (mul_eq_zero.mp hAB).resolve_right hB0])
    have hca₁ : ((⟨0, -2 * a, 0, a ^ 2 - 4 * b, 0⟩ : WeierstrassCurve ℚ)⁄
        (AlgebraicClosure ℚ)).a₁ = 0 := by
      simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map, map_zero]
    have hca₃ : ((⟨0, -2 * a, 0, a ^ 2 - 4 * b, 0⟩ : WeierstrassCurve ℚ)⁄
        (AlgebraicClosure ℚ)).a₃ = 0 := by
      simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map, map_zero]
    have hca₆ : ((⟨0, -2 * a, 0, a ^ 2 - 4 * b, 0⟩ : WeierstrassCurve ℚ)⁄
        (AlgebraicClosure ℚ)).a₆ = 0 := by
      simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map, map_zero]
    have hca₂ : ((⟨0, -2 * a, 0, a ^ 2 - 4 * b, 0⟩ : WeierstrassCurve ℚ)⁄
        (AlgebraicClosure ℚ)).a₂ = -2 * A := by
      simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map, map_mul, map_neg,
        map_ofNat, ← hA]
    exact (Affine.Point.add_eq_of_line two_ne_zero hca₁ hca₃ hca₆ _ _ _ hxy' hl₁' hl₂'
      (by rw [hca₂]; linear_combination hsum') hprod' hl₃').symm

/-- **Additivity of the explicit `2`-isogeny** (DERIVED 2026-07-25 from
`twoIsogenyFun_two_torsion_add` and the generic case `twoIsogenyFun_add_of_ne`): the
explicit map `φ(x, y) = (y²/x², y (b − x²)/x²)` from `y² = x³ + a x² + b x` to
`y² = x³ − 2 a x² + (a² − 4 b) x` (with `0` and `(0, 0)` sent to `0`) is a group
homomorphism. -/
theorem twoIsogenyFun_add (a b : ℚ)
    [(⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ).IsElliptic]
    (P Q : ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).Point) :
    twoIsogenyFun a b (P + Q) = twoIsogenyFun a b P + twoIsogenyFun a b Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · rw [← Point.zero_def, zero_add, twoIsogenyFun_zero, zero_add]
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rw [← Point.zero_def, add_zero, twoIsogenyFun_zero, add_zero]
  rcases eq_or_ne x₁ 0 with hx₁ | hx₁
  · have hy₁ : y₁ = 0 := normalForm_y_eq_zero_of_x_eq_zero a b h₁.1 hx₁
    subst hx₁
    subst hy₁
    exact twoIsogenyFun_two_torsion_add a b h₁ h₂
  rcases eq_or_ne x₂ 0 with hx₂ | hx₂
  · have hy₂ : y₂ = 0 := normalForm_y_eq_zero_of_x_eq_zero a b h₂.1 hx₂
    subst hx₂
    subst hy₂
    rw [add_comm (Affine.Point.some x₁ y₁ h₁),
      add_comm (twoIsogenyFun a b (Affine.Point.some x₁ y₁ h₁))]
    exact twoIsogenyFun_two_torsion_add a b h₂ h₁
  by_cases hxy : x₁ = x₂ ∧
      y₁ = ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).negY x₂ y₂
  · have hy : y₁ = -y₂ := by
      rw [hxy.2, Affine.negY]
      simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map, map_zero]
      ring
    rw [Point.add_of_Y_eq hxy.1 hxy.2, twoIsogenyFun_zero,
      twoIsogenyFun_some_of_ne_zero a b h₁ hx₁, twoIsogenyFun_some_of_ne_zero a b h₂ hx₂]
    refine (Point.add_of_Y_eq ?_ ?_).symm
    · rw [hxy.1, hy]; ring
    · rw [Affine.negY]
      simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map, map_zero, map_mul,
        map_sub, map_pow, map_neg, map_ofNat]
      rw [hxy.1, hy]
      field_simp
      ring
  · exact twoIsogenyFun_add_of_ne a b h₁ h₂ hx₁ hx₂ hxy

end WeierstrassCurve

/-- **The classical `2`-isogeny, in normal form** (DERIVED 2026-07-25 from
the explicit machinery above — `twoIsogenyFun` with its Galois
equivariance `twoIsogenyFun_map`, its kernel `twoIsogenyFun_eq_zero_iff`
and its additivity `twoIsogenyFun_add`, whose generic case
`twoIsogenyFun_add_of_ne` was PROVEN 2026-07-25): for
`E₀ : y² = x³ + a x² + b x` over `ℚ`, an elliptic curve (so
`Δ = 16 b² (a² − 4 b) ≠ 0`), the quotient of `E₀` by the order-`2`
subgroup `{0, (0, 0)}` is the elliptic curve
`E₀' : y² = x³ − 2 a x² + (a² − 4 b) x`, and the quotient isogeny on
points is

  `φ(x, y) = (y²/x², y (b − x²)/x²)` for `x ≠ 0`,
  `φ(0, 0) = φ(0) = 0`,

a group homomorphism with kernel exactly `{0, (0, 0)}`, Galois-
equivariant because its coordinate functions are rational functions
with `ℚ`-coefficients (so they commute with every `σ ∈ Gal(ℚ̄/ℚ)`).
The dual isogeny is given by the same formulas for `E₀'`, and
`φ̂ ∘ φ = [2]`. Vélu 1971 (kernel `{0, (0,0)}`); Silverman AEC III.4.5,
X.4.9 and Exercise 3.13. -/
theorem WeierstrassCurve.exists_quotient_isogeny_of_normalForm_two_torsion
    (a b : ℚ) [(⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ).IsElliptic]
    (h00 : ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).Nonsingular
      0 0) :
    ∃ (E' : WeierstrassCurve ℚ) (_ : E'.IsElliptic)
      (φ : ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).Point →+
        (E'⁄(AlgebraicClosure ℚ)).Point),
      (∀ (σ : Field.absoluteGaloisGroup ℚ)
        (Pt : ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).Point),
        φ (Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom Pt) =
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom (φ Pt)) ∧
      (∀ Pt : ((⟨0, a, 0, b, 0⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).Point,
        φ Pt = 0 ↔ Pt = 0 ∨ Pt = Affine.Point.some 0 0 h00) := by
  refine ⟨⟨0, -2 * a, 0, a ^ 2 - 4 * b, 0⟩, inferInstance,
    AddMonoidHom.mk' (WeierstrassCurve.twoIsogenyFun a b)
      (fun P Q => WeierstrassCurve.twoIsogenyFun_add a b P Q), ?_, ?_⟩
  · intro σ Pt
    exact WeierstrassCurve.twoIsogenyFun_map a b _ Pt
  · intro Pt
    exact WeierstrassCurve.twoIsogenyFun_eq_zero_iff a b h00 Pt

/-- **The rational two-torsion quotient isogeny — the classical
`2`-isogeny** (PROVEN, cut out of
`exists_quotient_isogeny_of_prime_card` 2026-07-23): for a RATIONAL
`2`-torsion point `T ≠ 0` of an elliptic curve `E/ℚ` there are an
elliptic curve `E'/ℚ` (the quotient `E/⟨T⟩`) and a Galois-equivariant
group homomorphism `E(ℚ̄) →+ E'(ℚ̄)` whose kernel is exactly
`{0, T}`. This is the classical `2`-isogeny with explicit formulas:
after translating `T` to `(0, 0)` the curve reads
`y² + a₁xy + a₃y = x³ + a₂x² + a₄x` and the quotient is
`y² + a₁xy + a₃y = x³ + a₂x² + (a₄ - 5t)x + (a₆' …)` with
`φ(x, y) = (x + t/x + …, …)` (Vélu 1971 for the kernel `{0, (0,0)}`;
Silverman AEC III.4.5 and X.4.9). -/
theorem WeierstrassCurve.exists_quotient_isogeny_of_rational_two_torsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (T : (E⁄ℚ).Point) (hT2 : T + T = 0) (hT0 : T ≠ 0) :
    ∃ (E' : WeierstrassCurve ℚ) (_ : E'.IsElliptic)
      (φ : (E⁄(AlgebraicClosure ℚ)).Point →+ (E'⁄(AlgebraicClosure ℚ)).Point),
      (∀ (σ : Field.absoluteGaloisGroup ℚ)
        (Pt : (E⁄(AlgebraicClosure ℚ)).Point),
        φ (Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom Pt) =
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom (φ Pt)) ∧
      (∀ Pt : (E⁄(AlgebraicClosure ℚ)).Point,
        φ Pt = 0 ↔ Pt = 0 ∨
          Pt = Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) T) := by
  classical
  -- normalise: `E ≅ y² = x³ + a x² + b x` with `T ↦ (0, 0)`
  obtain ⟨a, b, hell, h00, Ψ, hΨgal, hΨT⟩ :=
    E.exists_normalForm_pointEquiv_of_rational_two_torsion T hT2 hT0
  haveI := hell
  -- the explicit `2`-isogeny of the normal form
  obtain ⟨E', hE', φ₀, hφ₀gal, hφ₀ker⟩ :=
    WeierstrassCurve.exists_quotient_isogeny_of_normalForm_two_torsion a b h00
  -- transport it back along the normalising isomorphism
  refine ⟨E', hE', φ₀.comp Ψ.toAddMonoidHom, ?_, ?_⟩
  · intro σ Pt
    show φ₀ (Ψ (Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom Pt)) =
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom (φ₀ (Ψ Pt))
    rw [hΨgal σ Pt, hφ₀gal σ (Ψ Pt)]
  · intro Pt
    show φ₀ (Ψ Pt) = 0 ↔ _
    rw [hφ₀ker (Ψ Pt)]
    constructor
    · rintro (h | h)
      · exact Or.inl (Ψ.injective (h.trans (map_zero Ψ).symm))
      · exact Or.inr (Ψ.injective (h.trans hΨT.symm))
    · rintro (rfl | rfl)
      · exact Or.inl (map_zero Ψ)
      · exact Or.inr hΨT

/-- **The odd-prime-order quotient isogeny — Vélu's construction**
(DERIVED 2026-07-25 from `WeierstrassCurve.exists_velu_quotient_isogeny`
in `Fermat/FLT/EllipticCurve/Velu.lean`, which performs Vélu's
construction for an ARBITRARY finite Galois-stable subgroup of ODD order
— primality is never used — and where the remaining sorry leaves now
live: `isElliptic_of_three_twoTorsion`, `velu_exists_three_twoTorsion`,
`velu_pole_identity`, `velu_map_add_of_notMem`): for a
Galois-stable cyclic subgroup `C` of ODD prime order `ℓ` in the
geometric points of an elliptic curve `E/ℚ` there are an elliptic
curve `E'/ℚ` (the quotient `E/C`) and a Galois-equivariant group
homomorphism `E(ℚ̄) →+ E'(ℚ̄)` (the quotient isogeny on points) with
kernel exactly `C`. Vélu's explicit formulas (Vélu 1971; Silverman AEC
III.4.12 and Exercise 3.13) give the quotient curve's Weierstrass
coefficients as symmetric functions of the coordinates of the nonzero
points of `C` — rational because `C` is Galois-stable — and the
isogeny's coordinate functions as explicit rational functions; none of
this is in mathlib yet.

**Route audit (2026-07-25), SUPERSEDED the same day — do not dispatch
here.** The first audit concluded that this node does not decompose
further at this level: unlike the `2`-isogeny case (split into a
normalisation brick and a normal-form-formula brick), the odd case has no
coordinate normalisation to hide behind, since the points of `C` are not
individually rational, so any honest cut must produce the quotient curve
and the map TOGETHER. That is correct about the geometry and wrong about
the cut. The construction was carried out in
`Fermat/FLT/EllipticCurve/Velu.lean` by writing Vélu's map in its
GROUP-LAW form,

  `X(P) = x(P) + Σ_{Q ∈ C ∖ 0} (x(P + Q) − x(Q))`  (likewise `Y`),

which needs no representatives of `C ∖ {0}` modulo `±` — Vélu's `t` and
`w` are recovered as HALF the sums of the `±`-invariant terms over all of
`C ∖ {0}`, which is where oddness (not primality) is used — and which
makes Galois equivariance and the kernel immediate rather than a
rational-function computation. Both are proven there, as is the descent of
`t` and `w` to `ℚ` by `InfiniteGalois.mem_range_algebraMap_iff_fixed`.

What survives as open is exactly the geometry. **`velu_isElliptic`,
`velu_equation` and `velu_map_add` themselves are PROVEN** (2026-07-26)
and are transitively sorried CONSUMERS, not leaves — harvesting leaf
names from this paragraph as it read before that date produced phantom
dispatches. As of 2026-07-26 the direct leaves are
`isElliptic_of_three_twoTorsion` (three affine `2`-torsion points with
distinct `x` force `Δ ≠ 0`), `velu_exists_three_twoTorsion` (the quotient
curve has three such points over `F̄`), `velu_pole_identity` (the `y`-free
rational-function identity in `x` alone that remains of Vélu's
verification once `velu_equation_pole` has completed the square) and
`velu_map_add_of_notMem` (additivity when `P`, `Q`, `P + Q` all lie
outside the kernel); see their docstrings for routes. Vélu 1971 p. 238;
Kohel's thesis §2.4; Washington, *Elliptic Curves*, ch. 12. -/
theorem WeierstrassCurve.exists_quotient_isogeny_of_odd_prime_card
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (C : AddSubgroup ((E⁄(AlgebraicClosure ℚ)).Point))
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : Odd ℓ) (hcard : Nat.card C = ℓ)
    (hCstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ C,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈ C) :
    ∃ (E' : WeierstrassCurve ℚ) (_ : E'.IsElliptic)
      (φ : (E⁄(AlgebraicClosure ℚ)).Point →+ (E'⁄(AlgebraicClosure ℚ)).Point),
      (∀ (σ : Field.absoluteGaloisGroup ℚ)
        (Pt : (E⁄(AlgebraicClosure ℚ)).Point),
        φ (Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom Pt) =
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom (φ Pt)) ∧
      (∀ Pt : (E⁄(AlgebraicClosure ℚ)).Point, φ Pt = 0 ↔ Pt ∈ C) := by
  have hfin : (C : Set ((E⁄(AlgebraicClosure ℚ)).Point)).Finite := by
    rw [← Set.finite_coe_iff]
    exact Nat.finite_of_card_ne_zero
      (show Nat.card C ≠ 0 by rw [hcard]; exact hℓ.ne_zero)
  have hoddC : Odd (Nat.card C) := hcard ▸ hodd
  exact E.exists_velu_quotient_isogeny C hfin hoddC hCstable

set_option backward.isDefEq.respectTransparency false in
/-- **The prime-order quotient isogeny** (DERIVED 2026-07-23 from the
rational `2`-isogeny leaf `exists_quotient_isogeny_of_rational_two_torsion`
and the odd-order Vélu node `exists_quotient_isogeny_of_odd_prime_card`,
itself DERIVED 2026-07-25 from `Fermat/FLT/EllipticCurve/Velu.lean`):
for a Galois-stable cyclic subgroup `C` of prime order `ℓ` there is a
quotient isogeny with kernel exactly `C`. For odd `ℓ` this is the Vélu
leaf verbatim; for `ℓ = 2` the subgroup is `{0, t}` with `t` its unique
nonzero element, which is Galois-FIXED (stability moves `t` to a
nonzero element of `C`, i.e. to `t`), hence descends to a rational
`2`-torsion point (`exists_point_eq_baseChange_of_fixed`), and the
rational `2`-isogeny leaf applies. -/
theorem WeierstrassCurve.exists_quotient_isogeny_of_prime_card
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (C : AddSubgroup ((E⁄(AlgebraicClosure ℚ)).Point))
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hcard : Nat.card C = ℓ)
    (hCstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ C,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈ C) :
    ∃ (E' : WeierstrassCurve ℚ) (_ : E'.IsElliptic)
      (φ : (E⁄(AlgebraicClosure ℚ)).Point →+ (E'⁄(AlgebraicClosure ℚ)).Point),
      (∀ (σ : Field.absoluteGaloisGroup ℚ)
        (Pt : (E⁄(AlgebraicClosure ℚ)).Point),
        φ (Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom Pt) =
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom (φ Pt)) ∧
      (∀ Pt : (E⁄(AlgebraicClosure ℚ)).Point, φ Pt = 0 ↔ Pt ∈ C) := by
  classical
  rcases hℓ.eq_two_or_odd' with h2 | hodd
  · -- `ℓ = 2`: extract the unique nonzero element of `C`
    subst h2
    obtain ⟨a, b, hab, huniv⟩ := Nat.card_eq_two_iff.mp hcard
    have hall : ∀ z : C, z = a ∨ z = b := by
      intro z
      have hz : z ∈ ({a, b} : Set C) := by rw [huniv]; exact Set.mem_univ _
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hz
    have hextract : ∃ t : C, t ≠ 0 ∧ ∀ z : C, z = 0 ∨ z = t := by
      rcases hall 0 with h0 | h0
      · refine ⟨b, fun h => hab (h0.symm.trans h.symm), fun z => ?_⟩
        rcases hall z with hz' | hz'
        · exact Or.inl (hz'.trans h0.symm)
        · exact Or.inr hz'
      · refine ⟨a, fun h => hab (h.trans h0), fun z => ?_⟩
        rcases hall z with hz' | hz'
        · exact Or.inr hz'
        · exact Or.inl (hz'.trans h0.symm)
    obtain ⟨t, ht0, htall⟩ := hextract
    -- `t` is `2`-torsion: its double is an element of `C` equal to `t` or `0`
    have htt : t + t = 0 := by
      rcases htall (t + t) with h | h
      · exact h
      · exact absurd (add_left_cancel (a := t)
          (h.trans (add_zero t).symm)) ht0
    -- `t` is Galois-fixed: its image is a nonzero element of `C`
    have htfix : ∀ σ : Field.absoluteGaloisGroup ℚ,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom
          (t : (E⁄(AlgebraicClosure ℚ)).Point) =
        (t : (E⁄(AlgebraicClosure ℚ)).Point) := by
      intro σ
      have hmem : Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom
          (t : (E⁄(AlgebraicClosure ℚ)).Point) ∈ C := hCstable σ _ t.2
      rcases htall ⟨_, hmem⟩ with h | h
      · exfalso
        have h0 : Affine.Point.map
            (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom
            (t : (E⁄(AlgebraicClosure ℚ)).Point) = 0 :=
          congrArg Subtype.val h
        have hcoe : (t : (E⁄(AlgebraicClosure ℚ)).Point) = 0 :=
          Affine.Point.map_injective
            (f := (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom)
            (by rw [h0, map_zero])
        exact ht0 (Subtype.ext hcoe)
      · exact congrArg Subtype.val h
    -- descend `t` to a rational `2`-torsion point
    obtain ⟨T, hT⟩ := WeierstrassCurve.exists_point_eq_baseChange_of_fixed E
      (t : (E⁄(AlgebraicClosure ℚ)).Point) htfix
    have hT2 : T + T = 0 := by
      apply Affine.Point.map_injective (f := Algebra.ofId ℚ (AlgebraicClosure ℚ))
      rw [map_add, map_zero]
      show Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) T +
        Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) T = 0
      rw [hT]
      exact_mod_cast congrArg Subtype.val htt
    have hT0 : T ≠ 0 := by
      intro h
      refine ht0 (Subtype.ext ?_)
      rw [← hT, h, map_zero]
      rfl
    -- the rational `2`-isogeny leaf, with kernel `{0, t} = C`
    obtain ⟨E', hE', φ, hφeq, hφker⟩ :=
      E.exists_quotient_isogeny_of_rational_two_torsion T hT2 hT0
    refine ⟨E', hE', φ, hφeq, fun Pt => ?_⟩
    rw [hφker Pt]
    constructor
    · rintro (rfl | hPt)
      · exact zero_mem C
      · rw [hPt, hT]
        exact t.2
    · intro hPt
      rcases htall ⟨Pt, hPt⟩ with h | h
      · exact Or.inl (congrArg Subtype.val h)
      · refine Or.inr ?_
        rw [hT]
        exact congrArg Subtype.val h
  · exact E.exists_quotient_isogeny_of_odd_prime_card C hℓ hodd hcard hCstable

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **The quotient isogeny by an arbitrary finite Galois-stable
subgroup** (DERIVED 2026-07-23 from the prime-order Vélu leaf
`exists_quotient_isogeny_of_prime_card` by strong induction on the
cardinality): for every finite Galois-stable subgroup `C` of the
geometric points of an elliptic curve `E/ℚ` there are an elliptic
curve `E'/ℚ` (the quotient `E/C`) and a Galois-equivariant group
homomorphism `E(ℚ̄) →+ E'(ℚ̄)` (the quotient isogeny on points) with
kernel exactly `C`. Induction step: for a prime `ℓ ∣ #C`, the stable
subgroup `C₀ = C ⊓ E[ℓ]` is nonzero (Cauchy) and, being a subgroup of
`E[ℓ]` with `#E[ℓ] = ℓ²`, has order `ℓ` (Vélu leaf) or `ℓ²` — in the
latter case `C₀ = E[ℓ]` and multiplication by `ℓ` is the quotient map.
Either way `C`'s image in the quotient is stable of cardinality
`< #C`; recurse and compose. -/
theorem WeierstrassCurve.exists_quotient_isogeny
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (C : AddSubgroup ((E⁄(AlgebraicClosure ℚ)).Point))
    (hCfin : (C : Set ((E⁄(AlgebraicClosure ℚ)).Point)).Finite)
    (hCstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ C,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈ C) :
    ∃ (E' : WeierstrassCurve ℚ) (_ : E'.IsElliptic)
      (φ : (E⁄(AlgebraicClosure ℚ)).Point →+ (E'⁄(AlgebraicClosure ℚ)).Point),
      (∀ (σ : Field.absoluteGaloisGroup ℚ)
        (Pt : (E⁄(AlgebraicClosure ℚ)).Point),
        φ (Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom Pt) =
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom (φ Pt)) ∧
      (∀ Pt : (E⁄(AlgebraicClosure ℚ)).Point, φ Pt = 0 ↔ Pt ∈ C) := by
  classical
  suffices H : ∀ (n : ℕ) (E : WeierstrassCurve ℚ) (hE : E.IsElliptic)
      (C : AddSubgroup ((E⁄(AlgebraicClosure ℚ)).Point)),
      (C : Set ((E⁄(AlgebraicClosure ℚ)).Point)).Finite →
      (∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ C,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈ C) →
      Nat.card C = n →
      ∃ (E' : WeierstrassCurve ℚ) (_ : E'.IsElliptic)
        (φ : (E⁄(AlgebraicClosure ℚ)).Point →+ (E'⁄(AlgebraicClosure ℚ)).Point),
        (∀ (σ : Field.absoluteGaloisGroup ℚ)
          (Pt : (E⁄(AlgebraicClosure ℚ)).Point),
          φ (Affine.Point.map
            (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom Pt) =
          Affine.Point.map
            (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom (φ Pt)) ∧
        (∀ Pt : (E⁄(AlgebraicClosure ℚ)).Point, φ Pt = 0 ↔ Pt ∈ C) by
    exact H (Nat.card C) E inferInstance C hCfin hCstable rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro E hE C hCfin hCstable hcard
  haveI := hE
  haveI : Finite C := hCfin.to_subtype
  by_cases hbot : C = ⊥
  · -- trivial subgroup: the identity isogeny
    subst hbot
    exact ⟨E, hE, AddMonoidHom.id _, fun σ Pt => rfl, fun Pt => by
      simp [AddSubgroup.mem_bot]⟩
  -- a prime `ℓ` dividing the cardinality, and an element of order `ℓ` (Cauchy)
  have hCcard1 : Nat.card C ≠ 1 := fun h1 =>
    hbot (AddSubgroup.eq_bot_of_card_eq C h1)
  obtain ⟨ℓ, hℓprime, hℓdvd⟩ := Nat.exists_prime_and_dvd hCcard1
  haveI : Fact ℓ.Prime := ⟨hℓprime⟩
  haveI : Fintype C := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card] at hℓdvd
  obtain ⟨x₀, hx₀⟩ := exists_prime_addOrderOf_dvd_card (G := C) ℓ hℓdvd
  have hx₀ne : x₀ ≠ 0 := fun h => by
    rw [h, addOrderOf_zero] at hx₀
    exact hℓprime.one_lt.ne' hx₀.symm
  have hx₀torsion : (ℓ : ℤ) • (x₀ : (E⁄(AlgebraicClosure ℚ)).Point) = 0 := by
    have h1 : (ℓ : ℕ) • x₀ = 0 := by rw [← hx₀]; exact addOrderOf_nsmul_eq_zero x₀
    have h2 : (ℓ : ℕ) • (x₀ : (E⁄(AlgebraicClosure ℚ)).Point) = 0 := by
      have := congrArg (fun z : C => (z : (E⁄(AlgebraicClosure ℚ)).Point)) h1
      simpa using this
    rw [natCast_zsmul]
    exact h2
  -- the `ℓ`-torsion subgroup of the geometric points, of cardinality `ℓ²`
  let ℓtors : AddSubgroup ((E⁄(AlgebraicClosure ℚ)).Point) :=
    (Submodule.torsionBy ℤ ((E⁄(AlgebraicClosure ℚ)).Point) (ℓ : ℤ)).toAddSubgroup
  have hℓtors_mem : ∀ x : (E⁄(AlgebraicClosure ℚ)).Point,
      x ∈ ℓtors ↔ (ℓ : ℤ) • x = 0 := fun x =>
    (Submodule.mem_toAddSubgroup _).trans (Submodule.mem_torsionBy_iff _ _)
  have hℓtors_card : Nat.card ℓtors = ℓ ^ 2 :=
    TorsionCard.card_torsionBy (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) ℓ
      (Nat.cast_ne_zero.mpr hℓprime.ne_zero)
  -- the stable subgroup `C₀ = C ⊓ E[ℓ]`, nonzero by Cauchy
  set C₀ : AddSubgroup ((E⁄(AlgebraicClosure ℚ)).Point) := C ⊓ ℓtors with hC₀def
  have hC₀le : C₀ ≤ C := inf_le_left
  have hC₀tors : C₀ ≤ ℓtors := inf_le_right
  have hC₀stable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ C₀,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈ C₀ := by
    intro σ x hx
    rw [hC₀def, AddSubgroup.mem_inf] at hx ⊢
    refine ⟨hCstable σ x hx.1, ?_⟩
    rw [hℓtors_mem] at hx ⊢
    rw [← map_zsmul (Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom) (ℓ : ℤ) x,
      hx.2, map_zero]
  have hx₀C₀ : (x₀ : (E⁄(AlgebraicClosure ℚ)).Point) ∈ C₀ := by
    rw [hC₀def, AddSubgroup.mem_inf]
    exact ⟨x₀.2, (hℓtors_mem _).mpr hx₀torsion⟩
  have hC₀ne : C₀ ≠ ⊥ := fun h => by
    rw [h, AddSubgroup.mem_bot] at hx₀C₀
    exact hx₀ne (by exact_mod_cast hx₀C₀)
  -- `C₀ ≤ E[ℓ]` has order `ℓ` or `ℓ²` by Lagrange
  have hC₀dvd : Nat.card C₀ ∣ ℓ ^ 2 :=
    hℓtors_card ▸ AddSubgroup.card_dvd_of_le hC₀tors
  obtain ⟨k, hk2, hC₀card⟩ := (Nat.dvd_prime_pow hℓprime).mp hC₀dvd
  -- in either case, a quotient isogeny with kernel exactly `C₀`
  have hstep : ∃ (E₀ : WeierstrassCurve ℚ) (_ : E₀.IsElliptic)
      (φ₀ : (E⁄(AlgebraicClosure ℚ)).Point →+ (E₀⁄(AlgebraicClosure ℚ)).Point),
      (∀ (σ : Field.absoluteGaloisGroup ℚ)
        (Pt : (E⁄(AlgebraicClosure ℚ)).Point),
        φ₀ (Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom Pt) =
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom (φ₀ Pt)) ∧
      (∀ Pt : (E⁄(AlgebraicClosure ℚ)).Point, φ₀ Pt = 0 ↔ Pt ∈ C₀) := by
    interval_cases k
    · -- `#C₀ = 1` contradicts `C₀ ≠ ⊥`
      rw [pow_zero] at hC₀card
      exact absurd (AddSubgroup.eq_bot_of_card_eq _ hC₀card) hC₀ne
    · -- `#C₀ = ℓ`: the Vélu leaf
      rw [pow_one] at hC₀card
      exact E.exists_quotient_isogeny_of_prime_card C₀ hℓprime hC₀card hC₀stable
    · -- `#C₀ = ℓ²`: then `C₀ = E[ℓ]` and multiplication by `ℓ` quotients it
      have hC₀eq : C₀ = ℓtors := by
        have hsub : (C₀ : Set ((E⁄(AlgebraicClosure ℚ)).Point)) ⊆
            (ℓtors : Set ((E⁄(AlgebraicClosure ℚ)).Point)) := fun x hx =>
          hC₀tors hx
        have e1 : (ℓtors : Set ((E⁄(AlgebraicClosure ℚ)).Point)).ncard = ℓ ^ 2 :=
          hℓtors_card
        have e2 : (C₀ : Set ((E⁄(AlgebraicClosure ℚ)).Point)).ncard = ℓ ^ 2 :=
          hC₀card
        have hle : (ℓtors : Set ((E⁄(AlgebraicClosure ℚ)).Point)).ncard ≤
            (C₀ : Set ((E⁄(AlgebraicClosure ℚ)).Point)).ncard := by rw [e1, e2]
        have hfint : (ℓtors : Set ((E⁄(AlgebraicClosure ℚ)).Point)).Finite := by
          haveI : Finite ℓtors :=
            Nat.finite_of_card_ne_zero
              (by rw [hℓtors_card]; exact pow_ne_zero 2 hℓprime.ne_zero)
          exact Set.toFinite _
        exact SetLike.coe_injective (Set.eq_of_subset_of_ncard_le hsub hle hfint)
      refine ⟨E, hE, zsmulAddGroupHom (ℓ : ℤ), fun σ Pt => ?_, fun Pt => ?_⟩
      · rw [zsmulAddGroupHom_apply, zsmulAddGroupHom_apply]
        exact (map_zsmul (Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom)
          (ℓ : ℤ) Pt).symm
      · rw [zsmulAddGroupHom_apply, hC₀eq, hℓtors_mem]
  obtain ⟨E₀, hE₀, φ₀, hφ₀eq, hφ₀ker⟩ := hstep
  haveI := hE₀
  -- push `C` into the quotient: stable, finite, strictly smaller
  set C' : AddSubgroup ((E₀⁄(AlgebraicClosure ℚ)).Point) :=
    AddSubgroup.map φ₀ C with hC'def
  have hC'fin : (C' : Set ((E₀⁄(AlgebraicClosure ℚ)).Point)).Finite := by
    rw [hC'def, AddSubgroup.coe_map]
    exact hCfin.image _
  have hC'stable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ y ∈ C',
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom y ∈ C' := by
    intro σ y hy
    rw [hC'def, AddSubgroup.mem_map] at hy ⊢
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨Affine.Point.map
      (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x,
      hCstable σ x hx, hφ₀eq σ x⟩
  haveI : Finite C' := hC'fin.to_subtype
  haveI : Fintype C' := Fintype.ofFinite _
  have hlt : Nat.card C' < n := by
    -- the restriction of `φ₀` to `C` is onto `C'` but kills `x₀ ≠ 0`
    have hsurj : Function.Surjective (fun x : C =>
        (⟨φ₀ x, AddSubgroup.mem_map_of_mem φ₀ x.2⟩ : C')) := by
      rintro ⟨y, hy⟩
      rw [hC'def, AddSubgroup.mem_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨⟨x, hx⟩, rfl⟩
    have hnotinj : ¬ Function.Injective (fun x : C =>
        (⟨φ₀ x, AddSubgroup.mem_map_of_mem φ₀ x.2⟩ : C')) := by
      intro hinj
      have h0 : φ₀ (x₀ : (E⁄(AlgebraicClosure ℚ)).Point) = 0 :=
        (hφ₀ker _).mpr hx₀C₀
      have heq : (⟨φ₀ (x₀ : (E⁄(AlgebraicClosure ℚ)).Point),
          AddSubgroup.mem_map_of_mem φ₀ x₀.2⟩ : C') =
          ⟨φ₀ ((0 : C) : (E⁄(AlgebraicClosure ℚ)).Point),
          AddSubgroup.mem_map_of_mem φ₀ (0 : C).2⟩ := by
        apply Subtype.ext
        show φ₀ (x₀ : (E⁄(AlgebraicClosure ℚ)).Point) =
          φ₀ ((0 : C) : (E⁄(AlgebraicClosure ℚ)).Point)
        rw [h0, show ((0 : C) : (E⁄(AlgebraicClosure ℚ)).Point) = 0 from rfl,
          map_zero]
      exact hx₀ne (hinj heq)
    rw [← hcard, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_lt_of_surjective_not_injective _ hsurj hnotinj
  -- recurse on the image and compose
  obtain ⟨E', hE', φ₁, hφ₁eq, hφ₁ker⟩ :=
    ih (Nat.card C') hlt E₀ hE₀ C' hC'fin hC'stable rfl
  refine ⟨E', hE', φ₁.comp φ₀, fun σ Pt => ?_, fun Pt => ?_⟩
  · rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, hφ₀eq σ Pt,
      hφ₁eq σ (φ₀ Pt)]
  · rw [AddMonoidHom.comp_apply, hφ₁ker (φ₀ Pt)]
    constructor
    · intro hPt
      rw [hC'def, AddSubgroup.mem_map] at hPt
      obtain ⟨c, hc, hceq⟩ := hPt
      have h0 : φ₀ (Pt - c) = 0 := by rw [map_sub, hceq, sub_self]
      have hPtc : Pt - c ∈ C := hC₀le ((hφ₀ker _).mp h0)
      have hsum := add_mem hPtc hc
      simpa using hsum
    · intro hPt
      exact AddSubgroup.mem_map_of_mem φ₀ hPt

set_option backward.isDefEq.respectTransparency false in
/-- **The Vélu quotient node** (DERIVED 2026-07-22 from the
quotient-isogeny leaf `exists_quotient_isogeny` and the PROVEN
`2`-torsion embedding `freyCurve_two_torsion_embedding`): given a
Galois-stable line `W` in the `p`-torsion of the Frey curve on whose
quotient the Galois action is trivial, the quotient curve `E/C` by the
rational subgroup `C` corresponding to `W` (a `ℚ`-rational cyclic
subgroup of order `p`) is an elliptic curve over `ℚ` carrying a
rational point of order `p` (the image of any torsion point outside
`W`, Galois-fixed because the quotient action is trivial) and full
rational `2`-torsion (the image of the Frey curve's full `2`-torsion
through the odd-degree rational isogeny, injective on `2`-torsion). -/
theorem FreyPackage.exists_quotient_curve_point
    (P : FreyPackage)
    (W : Submodule (ZMod P.p)
      ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p))
    (_hW0 : W ≠ ⊥) (hWtop : W ≠ ⊤)
    (hstable : ∀ g : Field.absoluteGaloisGroup ℚ,
      ∀ v ∈ W, P.freyCurve.galoisRep P.p P.hppos g v ∈ W)
    (hquot : ∀ (g : Field.absoluteGaloisGroup ℚ)
      (v : (P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p),
      W.mkQ (P.freyCurve.galoisRep P.p P.hppos g v) = W.mkQ v) :
    ∃ (E' : WeierstrassCurve ℚ) (_ : E'.IsElliptic)
      (φ₂ : (ZMod 2 × ZMod 2) →+ (E'⁄ℚ).Point) (_ : Function.Injective φ₂)
      (Q : (E'⁄ℚ).Point), addOrderOf Q = P.p := by
  classical
  -- the inclusion of the `p`-torsion in the geometric point group
  let ι : ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) →+
      ((P.freyCurve)⁄(AlgebraicClosure ℚ)).Point :=
    { toFun := fun v => v.1
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hι : Function.Injective ι := fun v w h => Subtype.ext h
  -- the kernel subgroup `C ⊆ E(ℚ̄)`: the image of the line `W`
  let C : AddSubgroup (((P.freyCurve)⁄(AlgebraicClosure ℚ)).Point) :=
    AddSubgroup.map ι W.toAddSubgroup
  have hmemC : ∀ Pt : ((P.freyCurve)⁄(AlgebraicClosure ℚ)).Point,
      Pt ∈ C ↔ ∃ v ∈ W, ι v = Pt := by
    intro Pt
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, hv, rfl⟩
  have hcard : Nat.card
      ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) =
      P.p ^ 2 :=
    TorsionCard.card_torsionBy (P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ)))
      P.p (Nat.cast_ne_zero.mpr P.pp.ne_zero)
  haveI hNfin : Finite
      ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 P.pp.ne_zero)
  have hCfin : (↑C : Set (((P.freyCurve)⁄(AlgebraicClosure ℚ)).Point)).Finite := by
    rw [AddSubgroup.coe_map]
    exact (Set.toFinite _).image _
  have hCstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ C,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈ C := by
    intro σ x hx
    obtain ⟨v, hv, rfl⟩ := (hmemC x).mp hx
    have hcompat : Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom (ι v) =
        ι (P.freyCurve.galoisRep P.p P.hppos σ v) := rfl
    rw [hcompat]
    exact (hmemC _).mpr ⟨_, hstable σ v hv, rfl⟩
  obtain ⟨E', hE', φ, hφeq, hφker⟩ :=
    WeierstrassCurve.exists_quotient_isogeny P.freyCurve C hCfin hCstable
  haveI := hE'
  -- Part 1: a Galois-fixed point of exact order `p` on the quotient
  obtain ⟨v, -, hvW⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hWtop)
  have hQbar0 : φ (ι v) ≠ 0 := by
    intro h0
    obtain ⟨w, hw, hwv⟩ := (hmemC _).mp ((hφker _).mp h0)
    exact hvW (hι hwv ▸ hw)
  have hp_smul : P.p • φ (ι v) = 0 := by
    have h1 : P.p • (ι v) = 0 := by
      have h2 : ((P.p : ℕ) : ℤ) • (ι v) = 0 :=
        (Submodule.mem_torsionBy_iff _ _).mp v.2
      exact_mod_cast h2
    rw [← map_nsmul, h1, map_zero]
  have hordQbar : addOrderOf (φ (ι v)) = P.p := by
    have hdvd := addOrderOf_dvd_of_nsmul_eq_zero hp_smul
    rcases P.pp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h1) hQbar0
    · exact h1
  have hfixQ : ∀ σ : Field.absoluteGaloisGroup ℚ,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom (φ (ι v)) =
      φ (ι v) := by
    intro σ
    have hcompat : Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom (ι v) =
        ι (P.freyCurve.galoisRep P.p P.hppos σ v) := rfl
    have hsub : P.freyCurve.galoisRep P.p P.hppos σ v - v ∈ W := by
      have h := hquot σ v
      rwa [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h
    have hker : φ (ι (P.freyCurve.galoisRep P.p P.hppos σ v)) = φ (ι v) := by
      have hzero : φ (ι (P.freyCurve.galoisRep P.p P.hppos σ v) - ι v) = 0 :=
        (hφker _).mpr ((hmemC _).mpr ⟨_, hsub, map_sub ι _ _⟩)
      rw [map_sub, sub_eq_zero] at hzero
      exact hzero
    rw [← hφeq σ (ι v), hcompat]
    exact hker
  obtain ⟨Q, hQ⟩ :=
    WeierstrassCurve.exists_point_eq_baseChange_of_fixed E' (φ (ι v)) hfixQ
  have hordQ : addOrderOf Q = P.p := by
    rw [← hordQbar, ← hQ]
    exact (addOrderOf_injective _
      (Affine.Point.map_injective (f := Algebra.ofId ℚ (AlgebraicClosure ℚ))) Q).symm
  -- Part 2: the full rational `2`-torsion of the quotient
  obtain ⟨φ₂, hφ₂⟩ := P.freyCurve_two_torsion_embedding
  let ψ : (ZMod 2 × ZMod 2) →+ (E'⁄(AlgebraicClosure ℚ)).Point :=
    φ.comp ((Affine.Point.baseChange (W' := P.freyCurve) ℚ
      (AlgebraicClosure ℚ)).comp φ₂)
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    -- the image lies in `C`, which has exponent `p`, but is `2`-torsion
    have hmem : Affine.Point.baseChange (W' := P.freyCurve) ℚ
        (AlgebraicClosure ℚ) (φ₂ z) ∈ C :=
      (hφker _).mp hz
    obtain ⟨w, -, hw⟩ := (hmemC _).mp hmem
    have h2ann : ∀ w : ZMod 2 × ZMod 2, (2 : ℕ) • w = 0 := by decide
    have h2x : (2 : ℕ) •
        Affine.Point.baseChange (W' := P.freyCurve) ℚ (AlgebraicClosure ℚ)
          (φ₂ z) = 0 := by
      rw [← map_nsmul, ← map_nsmul, h2ann, map_zero, map_zero]
    have hpx : P.p •
        Affine.Point.baseChange (W' := P.freyCurve) ℚ (AlgebraicClosure ℚ)
          (φ₂ z) = 0 := by
      rw [← hw]
      have h2 : ((P.p : ℕ) : ℤ) • (ι w) = 0 :=
        (Submodule.mem_torsionBy_iff _ _).mp w.2
      exact_mod_cast h2
    have hcop : Nat.Coprime 2 P.p :=
      (Nat.coprime_primes Nat.prime_two P.pp).mpr (by have := P.hp5; omega)
    have hone : addOrderOf (Affine.Point.baseChange (W' := P.freyCurve) ℚ
        (AlgebraicClosure ℚ) (φ₂ z)) = 1 :=
      Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd
        (addOrderOf_dvd_of_nsmul_eq_zero h2x)
        (addOrderOf_dvd_of_nsmul_eq_zero hpx))
    have hz0 : φ₂ z = 0 := by
      apply Affine.Point.map_injective (f := Algebra.ofId ℚ (AlgebraicClosure ℚ))
      rw [map_zero]
      exact AddMonoid.addOrderOf_eq_one_iff.mp hone
    exact (injective_iff_map_eq_zero φ₂).mp hφ₂ z hz0
  have hfixψ : ∀ z : ZMod 2 × ZMod 2, ∀ σ : Field.absoluteGaloisGroup ℚ,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom (ψ z) =
      ψ z := by
    intro z σ
    show Affine.Point.map _ (φ (Affine.Point.baseChange (W' := P.freyCurve) ℚ
      (AlgebraicClosure ℚ) (φ₂ z))) = _
    rw [← hφeq σ _]
    exact congrArg φ (Affine.Point.map_baseChange
      (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom (φ₂ z))
  have hdesc : ∀ z : ZMod 2 × ZMod 2, ∃ Q₀ : (E'⁄ℚ).Point,
      Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) Q₀ = ψ z := fun z =>
    WeierstrassCurve.exists_point_eq_baseChange_of_fixed E' (ψ z) (hfixψ z)
  choose g hg using hdesc
  have hgadd : ∀ z z' : ZMod 2 × ZMod 2, g (z + z') = g z + g z' := by
    intro z z'
    apply Affine.Point.map_injective (f := Algebra.ofId ℚ (AlgebraicClosure ℚ))
    show Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) (g (z + z')) =
      Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) (g z + g z')
    rw [map_add, hg, hg, hg]
    exact map_add ψ z z'
  have hginj : Function.Injective (AddMonoidHom.mk' g hgadd) := by
    intro z z' hzz
    apply hψinj
    rw [← hg z, ← hg z']
    exact congrArg _ hzz
  exact ⟨E', hE', AddMonoidHom.mk' g hgadd, hginj, Q, hordQ⟩

/-- **Serre's reducible-case analysis for the Frey curve, given
Minkowski** (DERIVED 2026-07-17 from the stable-line dichotomy, the
PROVEN Galois descent for points, and the Vélu quotient leaf): if the
mod-`p` Galois representation on the `p`-torsion of the Frey curve is
not irreducible, and every finite-order mod-`p` character of `G_ℚ`
unramified at all finite places is trivial (the Minkowski input, taken
as a hypothesis — see `minkowski_character_trivial`), then either the
Frey curve itself has a rational point of order `p`, or some elliptic
curve over `ℚ` (the Vélu quotient `E/C` by the rational subgroup of
order `p`) has full rational `2`-torsion together with a rational point
of order `p`. -/
theorem FreyPackage.exists_p_point_of_not_isIrreducible_of_minkowski
    (P : FreyPackage)
    (hmink : ∀ χ : Field.absoluteGaloisGroup ℚ →* (ZMod P.p)ˣ,
      IsOpen (χ.ker : Set (Field.absoluteGaloisGroup ℚ)) →
      (∀ (q : ℕ) (hq : q.Prime),
        localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat ≤
          (χ.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker) →
      χ = 1)
    (h : ¬ (let E := P.freyCurve
            let p := P.p
            have : Fact p.Prime := ⟨P.pp⟩
            GaloisRep.IsIrreducible (E.galoisRep p P.hppos))) :
    (∃ Q : ((P.freyCurve)⁄ℚ).Point, addOrderOf Q = P.p) ∨
    (∃ (E' : WeierstrassCurve ℚ) (_ : E'.IsElliptic)
      (φ₂ : (ZMod 2 × ZMod 2) →+ (E'⁄ℚ).Point) (_ : Function.Injective φ₂)
      (Q : (E'⁄ℚ).Point), addOrderOf Q = P.p) := by
  rcases P.stable_line_dichotomy_of_not_isIrreducible hmink h with
    ⟨Pt, hord, hfix⟩ | ⟨W, hW0, hWtop, hstable, hquot⟩
  · -- the fixed point of order `p` descends to a rational point
    left
    obtain ⟨Q, hQ⟩ :=
      WeierstrassCurve.exists_point_eq_baseChange_of_fixed P.freyCurve Pt hfix
    refine ⟨Q, ?_⟩
    rw [← hord, ← hQ]
    exact (addOrderOf_injective _
      (Affine.Point.map_injective (f := Algebra.ofId ℚ (AlgebraicClosure ℚ))) Q).symm
  · -- the trivial-quotient line goes through the Vélu leaf
    right
    exact P.exists_quotient_curve_point W hW0 hWtop hstable hquot

/-- **Serre's reducible-case analysis for the Frey curve** (DERIVED
2026-07-16 from the two preceding nodes, by discharging the Minkowski
hypothesis with `minkowski_character_trivial`). -/
theorem FreyPackage.exists_p_point_of_not_isIrreducible
    (P : FreyPackage)
    (h : ¬ (let E := P.freyCurve
            let p := P.p
            have : Fact p.Prime := ⟨P.pp⟩
            GaloisRep.IsIrreducible (E.galoisRep p P.hppos))) :
    (∃ Q : ((P.freyCurve)⁄ℚ).Point, addOrderOf Q = P.p) ∨
    (∃ (E' : WeierstrassCurve ℚ) (_ : E'.IsElliptic)
      (φ₂ : (ZMod 2 × ZMod 2) →+ (E'⁄ℚ).Point) (_ : Function.Injective φ₂)
      (Q : (E'⁄ℚ).Point), addOrderOf Q = P.p) :=
  P.exists_p_point_of_not_isIrreducible_of_minkowski
    (fun χ hker hunram => minkowski_character_trivial χ hker hunram) h

/-- **Assembly of coprime torsion** (PROVEN 2026-07-16): in an abelian
group, an injective `(ℤ/2)²` and an element of order exactly `p` (an odd
prime) combine into an injective `ℤ/2 × ℤ/2p`, via the Chinese remainder
isomorphism `ℤ/2p ≅ ℤ/2 × ℤ/p`. The two images intersect trivially
because their exponents `2` and `p` are coprime. -/
theorem embedding_assembly {A : Type*} [AddCommGroup A]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (φ₂ : (ZMod 2 × ZMod 2) →+ A) (hφ₂ : Function.Injective φ₂)
    (Q : A) (hQ : addOrderOf Q = p) :
    ∃ ψ : (ZMod 2 × ZMod (2 * p)) →+ A, Function.Injective ψ := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr
    (Ne.symm hp2)
  -- the CRT isomorphism `ℤ/2p ≅ ℤ/2 × ℤ/p`
  let e : ZMod (2 * p) ≃+ ZMod 2 × ZMod p :=
    (ZMod.chineseRemainder hcop).toAddEquiv
  -- the `p`-part: `ℤ/p →+ A` sending `1 ↦ Q`
  have hpQ : (zmultiplesHom A Q) (p : ℤ) = 0 := by
    show (p : ℤ) • Q = 0
    rw [natCast_zsmul, ← hQ, addOrderOf_nsmul_eq_zero]
  let fQ : ZMod p →+ A := ZMod.lift p ⟨zmultiplesHom A Q, hpQ⟩
  have hfQ : ∀ k : ZMod p, fQ k = k.val • Q := by
    intro k
    have h1 : fQ (((k.val : ℤ) : ZMod p)) = zmultiplesHom A Q (k.val : ℤ) :=
      ZMod.lift_coe p _ (k.val : ℤ)
    rw [show (((k.val : ℤ)) : ZMod p) = k by
      rw [Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id]] at h1
    rw [h1]
    show ((k.val : ℤ)) • Q = _
    rw [natCast_zsmul]
  have hfQker : ∀ k : ZMod p, fQ k = 0 → k = 0 := by
    intro k hk
    rw [hfQ k] at hk
    have hdvd : addOrderOf Q ∣ k.val := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hk
    rw [hQ] at hdvd
    have hval0 : k.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt k)
    exact (ZMod.val_eq_zero k).mp hval0
  -- annihilation facts for the two parts
  have h2ann : ∀ y : ZMod 2 × ZMod 2, (2 : ℕ) • y = 0 := by decide
  have hpann : ∀ k : ZMod p, (p : ℕ) • k = 0 := by
    intro k
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  -- the assembled homomorphism
  let ψ : (ZMod 2 × ZMod (2 * p)) →+ A :=
    { toFun := fun x => φ₂ (x.1, (e x.2).1) + fQ (e x.2).2
      map_zero' := by
        have h0 : e 0 = 0 := map_zero e
        show φ₂ ((0 : ZMod 2 × ZMod (2 * p)).1, (e (0 : ZMod 2 × ZMod (2 * p)).2).1)
          + fQ (e (0 : ZMod 2 × ZMod (2 * p)).2).2 = 0
        rw [show ((0 : ZMod 2 × ZMod (2 * p)).2) = 0 from rfl, h0]
        rw [show (((0 : ZMod 2 × ZMod (2 * p)).1, ((0 : ZMod 2 × ZMod p)).1))
          = (0 : ZMod 2 × ZMod 2) from rfl,
          show ((0 : ZMod 2 × ZMod p)).2 = 0 from rfl, map_zero, map_zero, add_zero]
      map_add' := by
        intro x y
        have he : e (x.2 + y.2) = e x.2 + e y.2 := map_add e _ _
        rw [Prod.fst_add, Prod.snd_add, he, Prod.fst_add, Prod.snd_add,
          show (x.1 + y.1, (e x.2).1 + (e y.2).1)
            = (x.1, (e x.2).1) + (y.1, (e y.2).1) from rfl,
          map_add, map_add]
        abel }
  refine ⟨ψ, (injective_iff_map_eq_zero ψ).mpr ?_⟩
  intro x hx
  -- split `ψ x = 0` into the 2-part and the `p`-part
  set u := φ₂ (x.1, (e x.2).1) with hu
  set v := fQ (e x.2).2 with hv
  have huv : u + v = 0 := hx
  have h2u : (2 : ℕ) • u = 0 := by
    rw [hu, ← map_nsmul, h2ann, map_zero]
  have hpv : (p : ℕ) • v = 0 := by
    rw [hv, ← map_nsmul, hpann, map_zero]
  -- `p` odd kills the 2-part: `p•u = u` while `p•u = -p•v = 0`
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
  have hpu : (p : ℕ) • u = u := by
    have hstep : (p : ℕ) • u = m • ((2 : ℕ) • u) + u := by
      rw [← mul_nsmul', ← succ_nsmul]
      congr 1
      omega
    rw [hstep, h2u, smul_zero, zero_add]
  have hpu0 : (p : ℕ) • u = 0 := by
    have h := congrArg (fun z => (p : ℕ) • z) huv
    simpa [smul_add, hpv] using h
  have hu0 : u = 0 := by rw [← hpu, hpu0]
  have hv0 : v = 0 := by
    have := huv
    rw [hu0, zero_add] at this
    exact this
  -- conclude componentwise
  have h1 : (x.1, (e x.2).1) = 0 :=
    (injective_iff_map_eq_zero φ₂).mp hφ₂ _ hu0
  have h2 : (e x.2).2 = 0 := hfQker _ hv0
  have hex : e x.2 = 0 := by
    have hfst : (e x.2).1 = 0 := congrArg Prod.snd h1
    exact Prod.ext hfst h2
  have hx2 : x.2 = 0 := e.injective (by rw [hex, map_zero])
  have hx1 : x.1 = 0 := congrArg Prod.fst h1
  exact Prod.ext hx1 hx2

/-- **Serre's core, packaged with the 2-torsion** (DERIVED 2026-07-16 from
`exists_p_point_of_not_isIrreducible` and the PROVEN
`freyCurve_two_torsion_embedding`): if the mod-`p` representation of the
Frey curve is not irreducible, then some elliptic curve over `ℚ` has full
rational `2`-torsion and a rational point of order exactly `p`. In the
first case of the disjunction the curve is the Frey curve itself, whose
full rational `2`-torsion is proven; in the second the package is
supplied whole. -/
theorem FreyPackage.exists_two_torsion_and_p_point_of_not_isIrreducible
    (P : FreyPackage)
    (h : ¬ (let E := P.freyCurve
            let p := P.p
            have : Fact p.Prime := ⟨P.pp⟩
            GaloisRep.IsIrreducible (E.galoisRep p P.hppos))) :
    ∃ (E' : WeierstrassCurve ℚ) (_ : E'.IsElliptic)
      (φ₂ : (ZMod 2 × ZMod 2) →+ (E'⁄ℚ).Point) (_ : Function.Injective φ₂)
      (Q : (E'⁄ℚ).Point), addOrderOf Q = P.p := by
  rcases P.exists_p_point_of_not_isIrreducible h with ⟨Q, hQ⟩ | hpkg
  · obtain ⟨φ₂, hφ₂⟩ := P.freyCurve_two_torsion_embedding
    exact ⟨P.freyCurve, inferInstance, φ₂, hφ₂, Q, hQ⟩
  · exact hpkg

/-- **Serre's reducible-case embedding** (DERIVED 2026-07-16 from
`exists_two_torsion_and_p_point_of_not_isIrreducible` and the PROVEN
`embedding_assembly`): if the mod-`p` representation of the Frey curve is
not irreducible, then some elliptic curve over `ℚ` has a subgroup of
rational points isomorphic to `ℤ/2 × ℤ/2p` — the full rational
`2`-torsion and the rational point of order `p` produced by Serre's
analysis, assembled through the Chinese remainder isomorphism. -/
theorem FreyPackage.exists_torsion_embedding_of_not_isIrreducible (P : FreyPackage)
    (h : ¬ (let E := P.freyCurve
            let p := P.p
            have : Fact p.Prime := ⟨P.pp⟩
            GaloisRep.IsIrreducible (E.galoisRep p P.hppos))) :
    ∃ (E' : WeierstrassCurve ℚ) (_ : E'.IsElliptic)
      (φ : (ZMod 2 × ZMod (2 * P.p)) →+ (E'⁄ℚ).Point), Function.Injective φ := by
  obtain ⟨E', hE', φ₂, hφ₂, Q, hQ⟩ :=
    P.exists_two_torsion_and_p_point_of_not_isIrreducible h
  have hp2 : P.p ≠ 2 := by
    have := P.hp5
    omega
  obtain ⟨ψ, hψ⟩ := embedding_assembly P.pp hp2 φ₂ hφ₂ Q hQ
  exact ⟨E', hE', ψ, hψ⟩

