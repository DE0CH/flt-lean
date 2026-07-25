/-
MazurTorsion.lean — own work for the Fermat project (not vendored from the
FLT project).

Decomposition of `FreyPackage.mazur` (irreducibility of the mod-`p` Galois
representation on the `p`-torsion of the Frey curve) into two explicit
sorry nodes, following Serre's argument (Duke Math. J. 54 (1987), §4.1):

* `FreyPackage.exists_torsion_embedding_of_not_isIrreducible` (sorry node):
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

* `WeierstrassCurve.mazur_classification` (sorry node): **Mazur's torsion
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
    `no_torsion_order_27_of_j` (Olson's CM torsion theorem).
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
* `not_two_torsion_and_five_point` (PROVEN 2026-07-25 modulo two
  arithmetic leaves — the earlier "IRREDUCIBLE" verdict is SUPERSEDED):
  full rational `2`-torsion plus a point of order `5`. The order-`5`
  point gives a Tate parameter `c ≠ 0` with `u¹²Δ_E = c⁵(c² − 11c − 1)`
  (`MazurTwoTen.exists_tate_disc_of_order_five`, sorry leaf), and full
  `2`-torsion makes `Δ_E` a square
  (`MazurTwoTen.exists_disc_sq_of_full_two_torsion`, PROVEN); together
  they force a rational point with `c ≠ 0` on the conductor-`20`,
  rank-`0` curve `v² = c³ − 11c² − c`, excluded by
  `MazurTwoTen.no_rational_solution` (PROVEN) down to the single
  descent leaf `MazurTwoTen.quartic_no_solution`
  (`e² = X⁴ − 11X²Y² − Y⁴` has no coprime nonzero solution). No
  modular curve is constructed anywhere.
* `not_two_four_torsion_and_three_point` (PROVEN 2026-07-25 modulo one
  quartic): a rational `ℤ/2 × ℤ/4` plus a point of order `3`
  (`X_1(2,12)`; Kenku, Mazur 1977 Thm 8). Its own IRREDUCIBLE audit was
  refuted the same day: halving one `2`-torsion point makes BOTH
  differences of abscissae squares, not just their product
  (`MazurTwoTwelve.halving_squares`), and the order-`3` point is an
  inflection, so the level structure cuts down by elementary algebra to
  the plane quartic leaf `MazurTwoTwelve.quartic_only_trivial`
  (`v² = (j²−1)(j²+3)` has no rational point with `v ≠ 0` — the
  conductor-`24` rank-`0` curve `24a`).
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
  `j(E) = −12288000`, the CM value of discriminant `−27`;
* `no_torsion_order_27_of_j` — Olson's theorem that a CM elliptic curve
  over `ℚ` has torsion in `{ℤ/1, ℤ/2, ℤ/3, ℤ/4, ℤ/6, (ℤ/2)²}`,

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
* the remaining half, `notPrimePow_mem_cyclicIsogenyDegrees`: a level
  with at least two distinct prime factors lies in
  `{6, 10, 12, 14, 15, 18, 21}` — exactly the non-prime-powers of the
  full list. This is where the bulk of Kenku's 1979–1982 work still
  sits, and it is the one node of the five that is not a single
  modular curve.

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

/-- **No rational cyclic `32`-isogeny** (sorry node — the level `X_0(32)`
of Kenku's prime-power determination): no elliptic curve over `ℚ`
carries a Galois-stable cyclic subgroup of order `32`.

`32 = 2⁵` is the smallest power of `2` absent from the Mazur–Kenku list
(`2, 4, 8, 16` are all present — realized simultaneously by the
conductor-`45` curve `[1,−1,0,0,−5]`, whose cyclic isogeny degrees are
`{1,2,4,8,16}`, as already recorded in the section note above), so by
divisor descent this single statement disposes of every `2^k` with
`k ≥ 5`.

IRREDUCIBLE at this mathlib pin: `X_0(32)` has genus `1` (recomputed
2026-07-25 from the standard formula: `μ = 48`, `ν₂ = ν₃ = 0`, `8`
cusps, so `g = 1 + 4 − 4 = 1`), and the statement is that its Jacobian —
an elliptic curve of Mordell–Weil rank `0` over `ℚ` — has only the eight
cusps as rational points. No modular curve and no Jacobian exists in
this development. (Ogg, "Rational points on certain elliptic modular
curves", Proc. Sympos. Pure Math. 24 (1973); subsumed in the
Mazur–Kenku classification.) -/
theorem WeierstrassCurve.not_cyclicIsogeny_thirtyTwo (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (g : (E⁄(AlgebraicClosure ℚ)).Point) (hg : addOrderOf g = 32)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    False :=
  sorry

/-- **No rational cyclic `81`-isogeny** (sorry node — the level `X_0(81)`
of Kenku's prime-power determination): no elliptic curve over `ℚ`
carries a Galois-stable cyclic subgroup of order `81`.

`81 = 3⁴` is the smallest power of `3` absent from the Mazur–Kenku list
(`3, 9, 27` are all present — `27` by the isogeny class `27a`), so by
divisor descent this single statement disposes of every `3^k` with
`k ≥ 4`.

IRREDUCIBLE at this mathlib pin: `X_0(81)` has genus `4` (recomputed
2026-07-25: `μ = 108`, `ν₂ = ν₃ = 0`, `12` cusps, so
`g = 1 + 9 − 6 = 4`), so this is a Chabauty/Jacobian-rank argument on a
genus-`4` curve, not an elliptic-curve computation. Nothing of the kind
exists in this development. (Kenku's series, 1979–1982.) -/
theorem WeierstrassCurve.not_cyclicIsogeny_eightyOne (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (g : (E⁄(AlgebraicClosure ℚ)).Point) (hg : addOrderOf g = 81)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    False :=
  sorry

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
J. London Math. Soc. (2) 23 (1981), 415–427. -/
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

/-- **No rational cyclic `p²`-isogeny for `p ≥ 7`** (sorry node — the
levels `X_0(p²)` of Kenku's prime-power determination): for a prime
`p ≥ 7`, no elliptic curve over `ℚ` carries a Galois-stable cyclic
subgroup of order `p²`.

Together with the three explicit levels above this is the whole
prime-power half: the composite prime powers in the Mazur–Kenku list are
`4, 8, 9, 16, 25, 27`, all supported on `p ∈ {2, 3, 5}`, so for `p ≥ 7`
even the square is already excluded, and divisor descent removes every
higher power at once.

Only finitely many `p` actually require an argument, though the
statement is uniform: by `prime_mem_cyclicIsogenyDegrees` (Mazur), a
cyclic `p²`-isogeny yields a cyclic `p`-isogeny, so `p` would have to lie
in `{7, 11, 13, 17, 19, 37, 43, 67, 163}`. The two smallest cases are the
classical ones — `X_0(49)` has genus `1` (`μ = 56`, `ν₂ = 0`, `ν₃ = 2`,
`8` cusps) and `X_0(169)` genus `8` (`μ = 182`, `ν₂ = ν₃ = 2`, `14`
cusps), the latter being exactly Kenku, "The modular curve `X_0(169)` and
rational isogeny", J. London Math. Soc. (2) 22 (1980), 239–244. For the
larger `p` the input is that only finitely many `j`-invariants admit a
rational `p`-isogeny at all, all of them known explicitly, and none of
them a cyclic `p²`-isogeny.

IRREDUCIBLE at this mathlib pin: every route runs through the rational
points of a modular curve of genus `≥ 1`, and neither modular curves nor
their Jacobians exist in this development. -/
theorem WeierstrassCurve.not_cyclicIsogeny_sq_of_prime_ge_seven
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hg : addOrderOf g = p ^ 2)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    False :=
  sorry

/-- **Kenku's cyclic-isogeny degrees with two distinct prime factors**
(sorry node — the non-prime-power half of the `X_0` input): if the cyclic
subgroup `⟨g⟩` generated by a geometric point `g` of an elliptic curve
`E/ℚ` has exact order `N ≥ 2` which is NOT a prime power, and is stable
under `Gal(ℚ̄/ℚ)`, then

  `N ∈ {6, 10, 12, 14, 15, 18, 21}`.

`¬ IsPrimePow N` together with `2 ≤ N` says exactly that `N` has at least
two distinct prime factors, and the seven listed values are exactly the
non-prime-powers of the full Mazur–Kenku list
`{1, …, 19, 21, 25, 27, 37, 43, 67, 163}`. So this is the complement of
the four prime-power nodes above, and it carries the bulk of Kenku's
1979–1982 work.

IRREDUCIBLE at this mathlib pin: it is a case-by-case determination of
`X_0(N)(ℚ)` for the surviving composite levels, on top of Mazur's prime
theorem (which bounds the primes dividing `N`) and the prime-power nodes
above (which bound the exponents), leaving explicit Mordell–Weil
computations at the genus-one levels and Chabauty-style arguments above
them. The individual levels are distributed over Kenku's papers —
`X_0(39)` (Math. Proc. Cambridge Philos. Soc. 85, 1979), `X_0(65)` and
`X_0(91)` (ibid. 87, 1980) — and the classification is completed in "On
the number of `ℚ`-isomorphism classes of elliptic curves in each
`ℚ`-isogeny class" (J. Number Theory 15, 1982). Nothing of this exists
in the development. -/
theorem WeierstrassCurve.notPrimePow_mem_cyclicIsogenyDegrees
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) {N : ℕ} (hN : 2 ≤ N)
    (hpp : ¬ IsPrimePow N) (hg : addOrderOf g = N)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    N ∈ ({6, 10, 12, 14, 15, 18, 21} : Finset ℕ) :=
  sorry

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
itself because being IN Kenku's list is no contradiction there. -/
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
    rw [map_zsmul]
    refine AddSubgroup.zsmul_mem _ ?_ k
    -- `Affine.Point.map_baseChange` is applied through an `exact` against a
    -- LOCALLY STATED goal rather than passed straight to `rw`: elaborated on
    -- its own, its implicit base curve `W'` unifies to a different (defeq but
    -- not syntactically equal) spelling than the one in the goal, and the
    -- rewrite then fails to find its own pattern.
    have hfix : Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom
        (Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) Q) =
        Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) Q :=
      Affine.Point.map_baseChange _ Q
    rw [hfix]
    exact AddSubgroup.mem_zmultiples _

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

/-- **No rational point of order `3` together with a rational point of
order `5`** (sorry node — the `X_1(15)` content in its level-structure
form): no elliptic curve over `ℚ` carries both. The hypotheses say
exactly that `E(ℚ) ⊇ ℤ/3 ⊕ ℤ/5 ≅ ℤ/15`, i.e. that `(E, P + Q)` is a
non-cuspidal rational point of `X_1(15)` — a curve of genus `1`
(recomputed 2026-07-25: `μ/12 = 8`, `16` cusps, so `g = 1 + 8 − 8 = 1`)
whose Jacobian has Mordell–Weil rank `0` over `ℚ`, so `X_1(15)(ℚ)` is
finite and cuspidal (Kubert; Ligozat; subsumed in Mazur 1977, Thm 8).

IRREDUCIBLE at this mathlib pin (audit 2026-07-25). Equivalent to
`no_torsion_order_15` below, but stated as the fibre product
`X_1(3) ×_{X_1(1)} X_1(5)` of two genus-`0` modular curves, which is
the shape any elementary attack must use. Routes checked and rejected:

* *The `X_0` / isogeny shortcut is NOT available here.* `15` is a
  rational cyclic isogeny degree: `[1,0,1,−1,−2]` of conductor `50` has
  isogeny-degree set `{1, 3, 5, 15}` (PARI/GP `ellisomat`, witness
  recomputed 2026-07-25), so `X_0(15)` has non-cuspidal rational points.
* *Divisor reduction fails by design.* The proper divisors `1, 3, 5` all
  lie in Mazur's allowed set.
* *Reduction plus Hasse only bounds the conductor.* `15 ∣ #Ẽ(𝔽_p)` at
  every good `p` (including `p = 2`, since `15` is odd), and
  `p + 1 + 2√p < 15` for `p ≤ 7`, so bad reduction is forced exactly at
  `2, 3, 5, 7`: `210 ∣ N_E`, and nothing more.

A formal proof needs the genus-`0` parametrisations of `X_1(3)` and
`X_1(5)` in Tate normal form (`X_1(5)`: `b = c`), their fibre product —
the genus-`1` curve `X_1(15)` — and a rank-`0` Mordell–Weil computation
for it; none of that exists here. -/
theorem WeierstrassCurve.not_order_three_and_order_five_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (P Q : (E⁄ℚ).Point)
    (hP : addOrderOf P = 3) (hQ : addOrderOf Q = 5) : False :=
  sorry

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
  theorem `x⁴ − y⁴ = z² → xyz = 0`, is built here as
  `sq_ne_quartic_sub_quartic`, since mathlib carries only `not_fermat_42`.
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
#### Fermat's *other* quartic theorem

Mathlib has `not_fermat_42 : a ≠ 0 → b ≠ 0 → a ^ 4 + b ^ 4 ≠ c ^ 2` but **not**
its companion `x ^ 4 - y ^ 4 = z ^ 2 → x * y * z = 0`. The latter is what the
`m + k` odd branch of the descent below needs, and it is built here from scratch
by Fermat's own infinite descent. The two branches of that descent are:

* `y` odd (so `z` even): the triple `(y², z, x²)` gives `y² = M² - N²`,
  `x² = M² + N²`, hence `(xy)² = M⁴ - N⁴` — the same equation with `|M| < |x|`;
* `y` even (so `z` odd): the triple `(z, y², x²)` gives `y² = 2MN`,
  `x² = M² + N²`, and `M`, `N` coprime with `MN` twice a square forces
  `{M, N} = {a², 2b²}`, i.e. `x² = a⁴ + 4b⁴`. Splitting *that* as the
  Pythagorean triple `(a², 2b², x)` gives `rs = b²` with `r, s` coprime, so
  `r = ρ²`, `s = σ²` and `a² = ρ⁴ - σ⁴` — again the same equation, now with
  `ρ⁴ ≤ x`.

Both branches strictly decrease `|x|`, so a minimal counterexample cannot exist.
-/

/-- If a product of two coprime integers is a square and the first factor is
positive, that factor is the square of a positive integer (PROVEN). -/
lemma pos_sq_of_gcd_eq_one {u v w : ℤ} (h : Int.gcd u v = 1) (heq : u * v = w ^ 2)
    (hu : 0 < u) : ∃ a : ℤ, 0 < a ∧ u = a ^ 2 := by
  obtain ⟨a, ha | ha⟩ := Int.sq_of_gcd_eq_one h heq
  · have ha0 : a ≠ 0 := by rintro rfl; rw [ha] at hu; norm_num at hu
    exact ⟨|a|, abs_pos.mpr ha0, by rw [ha, sq_abs]⟩
  · exfalso; rw [ha] at hu; linarith only [hu, sq_nonneg a]

/-- If `u * v` is positive and `u` is positive then `v` is positive (PROVEN). -/
lemma pos_right_of_mul_pos {u v : ℤ} (hu : 0 < u) (h : 0 < u * v) : 0 < v := by
  rcases lt_trichotomy v 0 with hv | hv | hv
  · exact absurd h (by nlinarith)
  · exact absurd h (by simp [hv])
  · exact hv

/-- A positive integer is at most its own square (PROVEN). -/
lemma self_le_sq {r : ℤ} (h : 0 < r) : r ≤ r ^ 2 := by nlinarith

/-- A leg of a Pythagorean triple is shorter than its hypotenuse (PROVEN). -/
lemma lt_of_sq_eq_add {M K x : ℤ} (hK : 0 < K) (hx : 0 < x) (h : x ^ 2 = M ^ 2 + K ^ 2) :
    M < x := by
  nlinarith [pow_pos hK 2, sq_nonneg (x - M), sq_nonneg (x + M)]

/-- `ρ < (ρ²)² + (σ²)²` for positive `ρ`, `σ` — the size estimate that makes the
second branch of the quartic descent strictly decreasing (PROVEN). -/
lemma lt_of_eq_quartic {ρ σ x : ℤ} (hρ : 0 < ρ) (hσ : 0 < σ)
    (h : x = (ρ ^ 2) ^ 2 + (σ ^ 2) ^ 2) : ρ < x :=
  by linarith only [h, self_le_sq hρ, self_le_sq (pow_pos hρ 2), pow_pos (pow_pos hσ 2) 2]

/-- **Fermat's other quartic theorem, in descent form** (PROVEN): there is no
solution of `x ^ 4 - y ^ 4 = z ^ 2` in positive integers with `x.natAbs < N`.
The induction on `N` is Fermat's infinite descent; see the section note above. -/
theorem quartic_diff_aux : ∀ N : ℕ, ∀ x y z : ℤ, x.natAbs < N → 0 < x → 0 < y → 0 < z →
    x ^ 4 - y ^ 4 ≠ z ^ 2 := by
  intro N
  induction N with
  | zero => intro x y z hN; exact absurd hN (Nat.not_lt_zero _)
  | succ N ih =>
    intro x y z hN hx hy hz heq
    by_cases hcop : Int.gcd x y = 1
    case neg =>
      -- a common prime factor of `x` and `y` divides out, giving a smaller solution
      obtain ⟨p, hp, hpx, hpy⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
      obtain ⟨x1, rfl⟩ := Int.natCast_dvd.mpr hpx
      obtain ⟨y1, rfl⟩ := Int.natCast_dvd.mpr hpy
      have hp0 : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
      have hx1 : 0 < x1 := pos_right_of_mul_pos hp0 hx
      have hy1 : 0 < y1 := pos_right_of_mul_pos hp0 hy
      have hpz : ((p : ℤ) ^ 2) ∣ z := by
        rw [← Int.pow_dvd_pow_iff (two_ne_zero), ← heq]
        exact ⟨x1 ^ 4 - y1 ^ 4, by ring⟩
      obtain ⟨z1, rfl⟩ := hpz
      have hz1 : 0 < z1 := pos_right_of_mul_pos (pow_pos hp0 2) hz
      refine ih x1 y1 z1 ?_ hx1 hy1 hz1 ?_
      · have h1 : 0 < x1.natAbs := Int.natAbs_pos.mpr hx1.ne'
        have h2 : 2 ≤ p := hp.two_le
        have h3 : ((p : ℤ) * x1).natAbs = p * x1.natAbs := by
          rw [Int.natAbs_mul, Int.natAbs_natCast]
        rw [h3] at hN
        have h4 : 2 * x1.natAbs ≤ p * x1.natAbs := Nat.mul_le_mul_right _ h2
        omega
      · have hp4 : ((p : ℤ)) ^ 4 ≠ 0 := pow_ne_zero _ hp0.ne'
        apply mul_left_cancel₀ hp4
        linear_combination heq
    case pos =>
      have hxy : IsCoprime x y := Int.isCoprime_iff_gcd_eq_one.mpr hcop
      have hT : PythagoreanTriple (y ^ 2) z (x ^ 2) := by
        delta PythagoreanTriple; linear_combination -heq
      have hyz : Int.gcd (y ^ 2) z = 1 := by
        apply Int.isCoprime_iff_gcd_eq_one.mp
        have h1 : IsCoprime (x ^ 4) (y ^ 4) := hxy.pow
        have h2 := h1.add_mul_right_left (-1)
        rw [show x ^ 4 + (-1) * y ^ 4 = z ^ 2 by linear_combination heq] at h2
        exact (h2.symm.of_isCoprime_of_dvd_left
          (pow_dvd_pow y (by norm_num))).of_isCoprime_of_dvd_right (dvd_pow_self z two_ne_zero)
      rcases hT.even_odd_of_coprime hyz with ⟨hye, hzo⟩ | ⟨hyo, hze⟩
      · -- `y` even, `z` odd: two Pythagorean classifications and `x² = a⁴ + 4b⁴`
        have hT' : PythagoreanTriple z (y ^ 2) (x ^ 2) := hT.symm
        have hzy : Int.gcd z (y ^ 2) = 1 := by rw [Int.gcd_comm]; exact hyz
        obtain ⟨M, K, e1, e2, e3, e4, e5, e6⟩ :=
          hT'.coprime_classification' hzy hzo (by positivity)
        have hy2 : (0 : ℤ) < y ^ 2 := pow_pos hy 2
        have hM0 : M ≠ 0 := by
          rintro rfl
          rw [show (2 : ℤ) * 0 * K = 0 by ring] at e2
          exact absurd e2 hy2.ne'
        have hMpos : 0 < M := lt_of_le_of_ne e6 (Ne.symm hM0)
        have hKpos : 0 < K :=
          pos_right_of_mul_pos (show (0 : ℤ) < 2 * M by positivity) (by rw [← e2]; exact hy2)
        obtain ⟨y1, hy1⟩ : ∃ y1, y = 2 * y1 := by
          have h2 : (2 : ℤ) ∣ y ^ 2 := Int.dvd_of_emod_eq_zero hye
          obtain ⟨y1, hy1⟩ := Int.Prime.dvd_pow' (k := 2) Nat.prime_two (by exact_mod_cast h2)
          exact ⟨y1, hy1⟩
        obtain ⟨a, b, ha, hb, hab, haodd, hxeq⟩ :
            ∃ a b : ℤ, 0 < a ∧ 0 < b ∧ Int.gcd (a ^ 2) (2 * b ^ 2) = 1 ∧ (a ^ 2) % 2 = 1 ∧
              x ^ 2 = (a ^ 2) ^ 2 + (2 * b ^ 2) ^ 2 := by
          rcases e5 with ⟨hMe, hKo⟩ | ⟨hMo, hKe⟩
          · -- `M` even
            obtain ⟨M1, hM1⟩ : ∃ M1, M = 2 * M1 := ⟨M / 2, by omega⟩
            have hM1pos : 0 < M1 := by omega
            have hprod : M1 * K = y1 ^ 2 := by
              apply mul_left_cancel₀ (show (4 : ℤ) ≠ 0 by norm_num)
              rw [hy1, hM1] at e2; linear_combination -e2
            have hgcd : Int.gcd M1 K = 1 := by
              apply Int.isCoprime_iff_gcd_eq_one.mp
              exact (Int.isCoprime_iff_gcd_eq_one.mpr e4).of_isCoprime_of_dvd_left
                ⟨2, by linarith only [hM1]⟩
            obtain ⟨α, hα, hαe⟩ := pos_sq_of_gcd_eq_one hgcd hprod hM1pos
            obtain ⟨β, hβ, hβe⟩ := pos_sq_of_gcd_eq_one (by rw [Int.gcd_comm]; exact hgcd)
              (show K * M1 = y1 ^ 2 by linarith only [hprod]) hKpos
            refine ⟨β, α, hβ, hα, ?_, ?_, ?_⟩
            · rw [← hβe, show 2 * α ^ 2 = M by rw [hM1, hαe], Int.gcd_comm]; exact e4
            · rw [← hβe]; exact hKo
            · rw [e3, ← hβe, show 2 * α ^ 2 = M by rw [hM1, hαe]]; ring
          · -- `K` even
            obtain ⟨K1, hK1⟩ : ∃ K1, K = 2 * K1 := ⟨K / 2, by omega⟩
            have hK1pos : 0 < K1 := by omega
            have hprod : M * K1 = y1 ^ 2 := by
              apply mul_left_cancel₀ (show (4 : ℤ) ≠ 0 by norm_num)
              rw [hy1, hK1] at e2; linear_combination -e2
            have hgcd : Int.gcd M K1 = 1 := by
              apply Int.isCoprime_iff_gcd_eq_one.mp
              exact (Int.isCoprime_iff_gcd_eq_one.mpr e4).of_isCoprime_of_dvd_right
                ⟨2, by linarith only [hK1]⟩
            obtain ⟨α, hα, hαe⟩ := pos_sq_of_gcd_eq_one hgcd hprod hMpos
            obtain ⟨β, hβ, hβe⟩ := pos_sq_of_gcd_eq_one (by rw [Int.gcd_comm]; exact hgcd)
              (show K1 * M = y1 ^ 2 by linarith only [hprod]) hK1pos
            refine ⟨α, β, hα, hβ, ?_, ?_, ?_⟩
            · rw [← hαe, show 2 * β ^ 2 = K by rw [hK1, hβe]]; exact e4
            · rw [← hαe]; exact hMo
            · rw [e3, ← hαe, show 2 * β ^ 2 = K by rw [hK1, hβe]]
        have hT2 : PythagoreanTriple (a ^ 2) (2 * b ^ 2) x := by
          delta PythagoreanTriple; linear_combination -hxeq
        obtain ⟨r, s, f1, f2, f3, f4, _f5, f6⟩ := hT2.coprime_classification' hab haodd hx
        have hb2 : (0 : ℤ) < b ^ 2 := pow_pos hb 2
        have hrs : r * s = b ^ 2 := by
          apply mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by norm_num); linear_combination -f2
        have hrne : r ≠ 0 := by
          rintro rfl; rw [zero_mul] at hrs; exact absurd hrs.symm hb2.ne'
        have hr0 : 0 < r := lt_of_le_of_ne f6 (Ne.symm hrne)
        have hs0 : 0 < s := pos_right_of_mul_pos hr0 (by rw [hrs]; exact hb2)
        obtain ⟨ρ, hρ, hρe⟩ := pos_sq_of_gcd_eq_one f4 hrs hr0
        obtain ⟨σ, hσ, hσe⟩ := pos_sq_of_gcd_eq_one (by rw [Int.gcd_comm]; exact f4)
          (show s * r = b ^ 2 by linarith only [hrs]) hs0
        refine ih ρ σ a ?_ hρ hσ ha ?_
        · have h4 : ρ < x := lt_of_eq_quartic hρ hσ (by rw [f3, hρe, hσe])
          have := Int.natAbs_lt_natAbs_of_nonneg_of_lt hρ.le h4
          omega
        · rw [hρe, hσe] at f1; linear_combination -f1
      · -- `y` odd, `z` even: `(xy)² = M⁴ - N⁴` with `|M| < |x|`
        obtain ⟨M, K, e1, e2, e3, e4, _e5, e6⟩ :=
          hT.coprime_classification' hyz hyo (by positivity)
        have hy2 : (0 : ℤ) < y ^ 2 := pow_pos hy 2
        have hM0 : M ≠ 0 := by
          rintro rfl
          have h : y ^ 2 + K ^ 2 = 0 := by linear_combination e1
          linarith only [h, hy2, sq_nonneg K]
        have hMpos : 0 < M := lt_of_le_of_ne e6 (Ne.symm hM0)
        have hKpos : 0 < K :=
          pos_right_of_mul_pos (show (0 : ℤ) < 2 * M by positivity) (by rw [← e2]; exact hz)
        have hMx : M < x := lt_of_sq_eq_add hKpos hx e3
        refine ih M K (x * y) ?_ hMpos hKpos (by positivity) ?_
        · have := Int.natAbs_lt_natAbs_of_nonneg_of_lt hMpos.le hMx
          omega
        · linear_combination (-(y ^ 2)) * e3 + (-(M ^ 2 + K ^ 2)) * e1

/-- **Fermat's other quartic theorem** (PROVEN — absent from mathlib, which has
only `not_fermat_42`): no nonzero integers satisfy `x ^ 4 - y ^ 4 = z ^ 2`.
Equivalently `x ^ 4 - y ^ 4 = z ^ 2 → x * y * z = 0`; the exclusion is sharp,
since `x = y`, `z = 0` and `y = 0`, `z = x ^ 2` are genuine solutions. -/
theorem sq_ne_quartic_sub_quartic {x y z : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    x ^ 4 - y ^ 4 ≠ z ^ 2 := by
  intro heq
  refine quartic_diff_aux (|x|.natAbs + 1) |x| |y| |z| (by omega)
    (abs_pos.mpr hx) (abs_pos.mpr hy) (abs_pos.mpr hz) ?_
  have e1 : |x| ^ 4 = x ^ 4 := by rw [pow_abs]; exact abs_of_nonneg (by positivity)
  have e2 : |y| ^ 4 = y ^ 4 := by rw [pow_abs]; exact abs_of_nonneg (by positivity)
  have e3 : |z| ^ 2 = z ^ 2 := by rw [pow_abs]; exact abs_of_nonneg (by positivity)
  rw [e1, e2, e3]; exact heq

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
  refine sq_ne_quartic_sub_quartic (x := c) (y := e) (z := 2 * m * k) ?_ ?_ ?_ ?_
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
*other* quartic theorem `sq_ne_quartic_sub_quartic` forces `c e · 2mk = 0`;
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
theorem `x⁴ − y⁴ = z² → xyz = 0` is genuinely absent, and is proved above as
`sq_ne_quartic_sub_quartic` by an independent infinite descent (see the
section note before it). It is what the first case needs; note it cannot be
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
(sorry node — the `X_1(16)` content in its descent form): if
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
EXACTLY ONE leaf remains — `MazurLevel18.no_rational_two_torsion_abscissa`,
the actual `X_1(18)` content, now a statement about one explicit
polynomial in two rational unknowns. Everything else is PROVEN here,
including the reduction to normal form
(`WeierstrassCurve.exists_tateNormalForm_of_order_nine`).

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
now an explicit Diophantine statement** (sorry node, cut 2026-07-25 out
of `not_order_two_and_order_nine_point`).

Along the level-`9` Tate family `c = d²(d − 1)`, `b = c(d² − d + 1)`,
away from the cusps `d ∈ {0, 1}` and `d³ − 6d² + 3d + 1 = 0` (the
vanishing locus of `Δ`, see `delta_param`), the `2`-division cubic
`4x³ + ((1 − c)² − 4b)x² − 2b(1 − c)x + b²` has NO rational root. The
plane curve `{(d, x)}` this cuts out IS `X_1(18)`: it is the degree-`3`
cover of the `d`-line `X_1(9) ≅ P¹` obtained by adjoining a
`2`-torsion abscissa, it has genus `2` (Riemann–Hurwitz: `2 = 3·(−2) +
8`, the discriminant of the cubic in `x` being
`d⁵(d − 1)⁷(d² − d + 1)(d³ − 6d² + 3d + 1)` up to squares), and its
rational points are exactly the cusps. Kenku–Ligozat–Kubert; subsumed
in Mazur 1977, Thm 8.

Evidence that the statement is TRUE as written (2026-07-25): an
exhaustive PARI/GP search over `d = p/q` in lowest terms with
`|p| ≤ 200`, `q ≤ 40` and `Δ ≠ 0` — `9785` nondegenerate values —
found no `d` for which the cubic has a rational root (untrusted
searcher, never a proof; but it rules out a transcription error in the
family, which is the failure mode that actually matters here, since a
mis-stated family would almost certainly admit small solutions). The
family itself was cross-checked independently: `ellorder` confirms
`(0,0)` has order exactly `9` on `[1−c, −b, −b, 0, 0]` for
`d = 2, …, 6`, and `elldisc` at `d = 2` gives `−124416`, matching
`delta_param`.

WHY THIS IS STILL HARD, and what a proof needs. `J_1(18)` is a
`2`-dimensional abelian variety of Mordell–Weil rank `0` over `ℚ`, and
the rational points of `X_1(18)` are cut out inside it. Three shortcuts
were checked and all fail:

* *No elliptic-curve quotient to descend on.* `S_2(Γ_0(18)) = 0`
  (`X_0(18)` has genus `0`), while all of the `2`-dimensional
  `S_2(Γ_1(18))` lies in the eigenspaces of a nebentypus of order `3`
  (PARI/GP `mfdim([18,2,0],1)` returns the single orbit with character
  `Mod(13,18)`, of order `3`). A weight-`2` newform with trivial
  character and rational coefficients — which is what an elliptic
  quotient of `J_1(18)` over `ℚ` would require — therefore does not
  exist at this level. So `J_1(18)` admits no elliptic curve quotient
  over `ℚ`, and the standard "map the genus-`2` curve to a rank-`0`
  elliptic curve and enumerate" argument is unavailable.
* *No local obstruction can exist.* The cusps are rational points of
  `X_1(18)`, so the curve has points everywhere locally; the content is
  that the rational points are ALL cuspidal, which no congruence
  argument can deliver.
* *The `X_0` / isogeny shortcut is unavailable* — see the parent
  docstring; `18` is a rational cyclic isogeny degree.

So a formal proof needs genus-`2` Jacobian arithmetic (Mumford
representation, the Abel–Jacobi embedding, and `J_1(18)(ℚ)` computed as
a finite group), none of which exists in mathlib at this pin. That is
the honest cost, and it is unchanged by this cut — what the cut buys is
that the remaining statement is elementary to STATE and can be attacked
directly, without any modular-curve theory. -/
theorem no_rational_two_torsion_abscissa (d b c x : ℚ)
    (hc : c = d ^ 2 * (d - 1)) (hb : b = c * (d ^ 2 - d + 1))
    (hd0 : d ≠ 0) (hd1 : d ≠ 1) (hcub : d ^ 3 - 6 * d ^ 2 + 3 * d + 1 ≠ 0)
    (hx : 4 * x ^ 3 + ((1 - c) ^ 2 - 4 * b) * x ^ 2 - 2 * b * (1 - c) * x + b ^ 2 = 0) :
    False :=
  sorry

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
here; the single surviving input is
`MazurLevel18.no_rational_two_torsion_abscissa`, the explicit
`X_1(18)` Diophantine statement. The hypotheses say
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
survives only for `MazurLevel18.no_rational_two_torsion_abscissa`, where
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

/-- **No rational point of order `21`** (sorry node — IRREDUCIBLE
literature citation, audited 2026-07-25): `X_1(21)` has genus `5` and
no non-cuspidal rational point (Kubert–Kenku–Ligozat; subsumed in
Mazur 1977, Thm 8).

By the criterion in the section note the `X_0` shortcut of
`mem_cyclicIsogenyDegrees` is NOT available here — `21` is one of the
three levels (`21, 25, 27`) that are in Kenku's list and have no
level-structure sharpening either, so these are the only bare sorry
nodes left among the eleven. `21` IS a
rational cyclic isogeny degree, so a rational `21`-isogeny is no
contradiction at all. `X_0(21)` is a genus-one curve of Mordell–Weil
rank `0` with non-cuspidal rational points; an explicit witness curve
carrying a rational cyclic `21`-isogeny is `[a₁,a₂,a₃,a₄,a₆] =
[1, −1, 0, 3, −1]`, of conductor `162` (found with PARI/GP
`ellisomat`; untrusted searcher, never a proof). Only the finer
`X_1(21)` statement — that none of the finitely many non-cuspidal
rational points of `X_0(21)` lifts to a rational point of order `21` —
excludes the point, and that needs `X_1(21)` itself.

Other routes checked and rejected:

* *Divisor reduction fails by design.* `21 = 3 · 7` and both `3` and
  `7` are permitted torsion orders, so neither the other levels nor
  `no_prime_torsion_ge_eleven` applies.
* *Reduction plus Hasse only bounds the conductor.* `21` is odd, so
  the point injects into `Ẽ(𝔽_p)` at every prime `p` of good
  reduction, `p = 2` included; `21 ≤ ⌊p + 1 + 2√p⌋` then forces bad
  reduction exactly at `2, 3, 5, 7, 11`, while at `p = 13` already
  `#Ẽ(𝔽_13) = 21` is Hasse-admissible (`a₁₃ = −7`, `|a₁₃| ≤ 2√13`).
  A lower bound on the conductor is never a contradiction.

A formal proof needs `X_1(21)` as an arithmetic curve over `ℚ`
together with a Chabauty-style determination of its rational points. -/
theorem WeierstrassCurve.no_torsion_order_21 (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (Q : (E⁄ℚ).Point) : addOrderOf Q ≠ 21 :=
  sorry

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

/-- **No rational point of order `25`** (sorry node — irreducible
literature citation): `X_1(25)` has genus `12` and no non-cuspidal
rational point (subsumed in Mazur 1977, Thm 8). The `X_0` shortcut is
NOT available at this level: a rational cyclic `25`-isogeny does exist
(the class `11a` contains one), so `X_0(25)` has non-cuspidal rational
points and only the `X_1` statement excludes an order-`25` point.

IRREDUCIBLE at this mathlib pin (audit 2026-07-25, re-audited the same
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
in which the classical proofs proceed. -/
theorem WeierstrassCurve.no_torsion_order_25 (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (Q : (E⁄ℚ).Point) : addOrderOf Q ≠ 25 :=
  sorry

/-- **`X_0(27)`: a rational cyclic `27`-subgroup forces
`j = −12288000`** (sorry node — the `X_0(27)` content, replacing the
former `X_1(27)` citation 2026-07-25): if the geometric points of an
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
curve rather than the rational points of a genus-`13` curve. -/
theorem WeierstrassCurve.j_of_stable_cyclic_subgroup_order_27
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) (hg : addOrderOf g = 27)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    E.j = -12288000 :=
  sorry

/-- **No rational point of order `27` on a curve of `j`-invariant
`−12288000`** (sorry node — the CM torsion content, 2026-07-25): the
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
field is not contained in `ℚ`). -/
theorem WeierstrassCurve.no_torsion_order_27_of_j (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (hj : E.j = -12288000) (Q : (E⁄ℚ).Point) :
    addOrderOf Q ≠ 27 :=
  sorry

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
   [`MazurTwoTen.exists_tate_disc_of_order_five`]
2. **Full `2`-torsion ⇒ `Δ_E` is a rational square.** The three
   `2`-torsion abscissae `θ₁, θ₂, θ₃` are the roots of the `2`-division
   cubic, and `Δ = 16((θ₁−θ₂)(θ₁−θ₃)(θ₂−θ₃))²`.
   [`MazurTwoTen.exists_disc_sq_of_full_two_torsion`, PROVEN]
3. Combining, `c(c² − 11c − 1)` is a rational square with `c ≠ 0`, i.e.
   a rational point on `v² = c³ − 11c² − c` with `c ≠ 0`.
   [`MazurTwoTen.no_rational_solution`, PROVEN modulo the descent]

The curve `v² = c³ − 11c² − c` is conductor `20`, Mordell–Weil rank `0`,
torsion `ℤ/2` generated by `(0,0)`; its only affine rational point is
`(0,0)` (PARI/GP `ellrank`/`elltors`/`ellratpoints`, used here only as
an untrusted searcher — the Lean proof is the elementary descent below).
Note this proves *more* than needed: no elliptic curve over `ℚ` with a
rational `5`-torsion point has square discriminant.
-/

/-- **The quartic of the `X_1(2,10)` descent** (sorry leaf — the
arithmetic heart of `not_two_torsion_and_five_point`): the quartic
`e² = X⁴ − 11X²Y² − Y⁴` has no solution in coprime nonzero integers.
This is the `2`-descent homogeneous space of the conductor-`20` curve
`v² = c³ − 11c² − c`; the statement is equivalent to that curve having
Mordell–Weil rank `0`, so it cannot be settled by a congruence alone
(the quartic has the rational point `(X, Y, e) = (1, 0, 1)`, i.e. it is
the *trivial* coset and is everywhere locally solvable).

VERIFIED NUMERICALLY: no solution with `1 ≤ X, Y ≤ 400` coprime; and
`ellratpoints` finds no point of height `≤ 10⁴` on `v² = c³ − 11c² − c`
beyond `(0,0)`.

ROUTE (classical infinite descent, worked out 2026-07-25; every step
checked by hand, none of it yet written in Lean):

* *Parity.* `X` must be odd and `4 ∣ Y`. Both odd gives
  `e² ≡ −11X²Y² ∈ {5, 13} (mod 16)`, neither a square; `X` even gives
  `e² ≡ 3` or `15 (mod 16)`; `X` odd with `Y ≡ 2 (mod 4)` gives
  `e² ≡ 5 (mod 16)`.
* *Sum of two squares.* Completing the square in `Y²` gives
  `B² + (2e)² = 125 X⁴` with `B = 2Y² + 11X² > 0`, `B` odd, `e` odd.
  An odd prime dividing `gcd(B, e)` divides `125X⁴`, and `p ∣ X` forces
  `p ∣ Y`; `p = 5` is excluded because `5 ∣ e` forces `Y² ≡ 2X² (mod 5)`
  and `2` is not a quadratic residue mod `5`. So `gcd(B, 2e) = 1`.
* *Gaussian factorisation.* `B ± 2ei` are then coprime in `ℤ[i]`, of
  odd norm, so (with `(2+i)³ = 2 + 11i` of norm `125`)
  `B + 2ei = u(2 + 11i)γ⁴` for a unit `u` and `γ = p + qi` with
  `N γ = X` and `gcd(p,q) = 1`. Parity of `R = Re γ⁴`, `S = Im γ⁴`
  (`R` odd, `4 ∣ S` since `X` is odd) forces `B = ±(11R + 2S)`.
* *Descent.* Using `R = X² − 8p²q²`, the two signs give
  `Y² = 4pq(p² − 11pq − q²)` and, after `P = p + q`, `Q = p − q`,
  `Y² = P(−Q)(P² − 11P(−Q) − (−Q)²)`. Both are the SAME shape
  `m'n'(m'² − 11m'n' − n'²) = □` that `no_coprime_solution` starts
  from, with `p² + q² = X` strictly smaller than `max(|m|, n)` — an
  infinite descent.

Formalising this needs `Mathlib.NumberTheory.Zsqrtd.GaussianInt`
(`ℤ[i]` is a `EuclideanDomain`, hence a UFD) together with
`exists_associated_pow_of_mul_eq_pow'` for the fourth-power extraction,
and a well-founded recursion on `m.natAbs + n.natAbs`. The natural
re-cut is a `descent_step` lemma producing a strictly smaller solution
of the same shape, wrapped in `Nat.strong_induction_on`. -/
theorem MazurTwoTen.quartic_no_solution {X Y e : ℤ} (hXY : IsCoprime X Y)
    (hX : X ≠ 0) (hY : Y ≠ 0) :
    e ^ 2 ≠ X ^ 4 - 11 * X ^ 2 * Y ^ 2 - Y ^ 4 :=
  sorry

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

/-- **Tate normal form at a rational point of order `5`** (sorry leaf):
if `E/ℚ` carries a rational point of order `5` then, for some nonzero
`c` and `u`, `u¹² Δ_E = c⁵(c² − 11c − 1)`.

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
   content, a division-polynomial/group-law computation.

For `E(c, c) : y² + (1−c)xy − cy = x³ − cx²` one computes
`b₂ = c² − 6c + 1`, `b₄ = c² − c`, `b₆ = c²`, `b₈ = −c³`, hence
`Δ = c⁵(c² − 11c − 1)` (verified symbolically). `c ≠ 0` because
`Δ ≠ 0`. The `u¹²` is `WeierstrassCurve.variableChange_Δ`
(`(C • W).Δ = C.u⁻¹ ^ 12 * W.Δ`), and either orientation of `u` is
equivalent since `u` ranges over all nonzero rationals.

MISSING MACHINERY, in dependency order, none of it in mathlib at this
pin: (a) transport of `WeierstrassCurve.Affine.Point` along a
`VariableChange` (mathlib has `Point.map` along ring homs but not along
a variable change); (b) the normal-form existence statement "a point of
order `≥ 4` can be moved to `(0,0)` with `a₄ = a₆ = 0` and `a₂ = a₃`";
(c) the translation of `addOrderOf Q = 5` into `b = c`, most cleanly via
`WeierstrassCurve.Ψ`/the `5`-division polynomial. -/
theorem MazurTwoTen.exists_tate_disc_of_order_five (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (Q : (E⁄ℚ).Point) (hQ : addOrderOf Q = 5) :
    ∃ c u : ℚ, u ≠ 0 ∧ c ≠ 0 ∧ u ^ 12 * E.Δ = c ^ 5 * (c ^ 2 - 11 * c - 1) :=
  sorry

/-- **No full rational `2`-torsion together with a rational point of
order `5`** (PROVEN 2026-07-25 modulo the two leaves
`MazurTwoTen.exists_tate_disc_of_order_five` and
`MazurTwoTen.quartic_no_solution`): no elliptic curve over `ℚ` has an
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
geometric-to-arithmetic passage is proven below. What is left is exactly
one Diophantine statement over `ℚ` — `MazurTwoTwelve.quartic_only_trivial`
— namely that the genus-`1` quartic `v² = (j² − 1)(j² + 3)` has no
rational point with `v ≠ 0`.

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
`h = de`; the case `d, e` both odd descends via
`(u,v)` with `h = u² − v²`, `g = ±2uv` to
`u⁴ − u²v² + v⁴ = ((d²+e²)/2)²`, and `f² − ((d²+e²)/2)² = 3(d²−e²)²/4`,
so the descent is strict unless `d² = e²`).
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

/-- **The rational points of `X_1(2,12)`, in plane-quartic form**
(sorry node, cut 2026-07-25 out of
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

Equivalent forms, in case one is easier to formalise:

* Substituting `u = j²` and `u + 1 = t + 1/t` turns it into
  `t(t² − t + 1) = □`, i.e. the Weierstrass curve `Y² = X³ − X² + X`
  (conductor `24`, rank `0`, torsion `ℤ/4` generated by `(1,1)`, so
  `E(ℚ) = {O, (0,0), (1,±1)}`).
* Writing `X = d²/e²` in lowest terms on that curve — the factor `X` is
  coprime to `X² − X + 1`, so each is a square — reduces it to the
  classical quartic `d⁴ − d²e² + e⁴ = f²` with `gcd(d, e) = 1`, whose
  only solutions have `d = 0`, `e = 0` or `d² = e²`.
* Setting `g = d² − e²`, `h = de` turns that into the concordant-forms
  system `g² + h² = □` and `g² + 4h² = □` with `gcd(g, h) = 1`, forcing
  `gh = 0`.

Descent sketch for the last form, where a Lean proof would go: `g, h`
cannot both be odd (`g² + h² ≡ 2 mod 4`). If `d, e` are both odd then
`h` is odd, `g` even; the primitive triple `g² + h² = f²` gives
`h = u² − v²`, `g = ±2uv`, `f = u² + v²`, and then
`g² + 4h² = (d² + e²)²` becomes `u⁴ − u²v² + v⁴ = ((d² + e²)/2)²`, a new
solution with `f² − ((d² + e²)/2)² = 3(d² − e²)²/4 > 0` unless
`d² = e²` — a strict descent. The opposite-parity case still needs a
descent step (the obvious one returns `{u, v} = {d, e}`); Mordell,
*Diophantine Equations*, treats `x⁴ − x²y² + y⁴ = z²` in full. -/
theorem MazurTwoTwelve.quartic_only_trivial (j v : ℚ)
    (h : v ^ 2 = (j ^ 2 - 1) * (j ^ 2 + 3)) :
    v = 0 :=
  sorry

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

/-- The prime of `𝓞 ℚ` attached to the prime number `q` is the span of
`q`: unfolding `toHeightOneSpectrumRingOfIntegersRat`, the ideal is the
comap of `span {(q : ℤ)}` along `Rat.ringOfIntegersEquiv`, and a ring
isomorphism carries spans of singletons to spans of singletons while
preserving the naturals. -/
lemma asIdeal_toHeightOneSpectrumRingOfIntegersRat {q : ℕ} (hq : q.Prime) :
    hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal =
      Ideal.span {(q : NumberField.RingOfIntegers ℚ)} := by
  have h1 : hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal =
      Ideal.comap (Rat.ringOfIntegersEquiv.symm.symm) (Ideal.span {(q : ℤ)}) := rfl
  rw [h1, RingEquiv.symm_symm, ← Ideal.map_symm, Ideal.map_span, Set.image_singleton,
    map_natCast]

open IsDedekindDomain.HeightOneSpectrum in
set_option maxHeartbeats 1000000 in
/-- `q` is a uniformizer of the completed integer ring `ℤ_q`: the maximal
ideal of `(ℤ_q)ˆ = 𝒪ᵥ` (for `v = v_q` the place of `ℚ` at `q`) is the
span of `q`. Via `maximalIdeal_eq_span_uniformizer` it suffices that the
valuation of `q` in `ℚ_q` is exactly `ofAdd (-1)`, which reduces through
`valuedAdicCompletion_eq_valuation` and `valuation_of_algebraMap` to the
`intValuation` of `q` in `𝓞 ℚ`, computed by `intValuation_singleton`
from `v_q = span {q}`. -/
lemma maximalIdeal_adicCompletionIntegers_eq_span {q : ℕ} (hq : q.Prime) :
    IsLocalRing.maximalIdeal
        (adicCompletionIntegers ℚ hq.toHeightOneSpectrumRingOfIntegersRat) =
      Ideal.span
        {(q : adicCompletionIntegers ℚ hq.toHeightOneSpectrumRingOfIntegersRat)} := by
  have hq0 : ((q : NumberField.RingOfIntegers ℚ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr hq.ne_zero
  have hval : hq.toHeightOneSpectrumRingOfIntegersRat.intValuation
      ((q : NumberField.RingOfIntegers ℚ)) = Multiplicative.ofAdd (-1 : ℤ) :=
    hq.toHeightOneSpectrumRingOfIntegersRat.intValuation_singleton hq0
      (asIdeal_toHeightOneSpectrumRingOfIntegersRat hq)
  apply adicCompletion.maximalIdeal_eq_span_uniformizer
  -- the valuation of `q` in `ℚ_q`, assembled entirely in the mathlib
  -- lemmas' own coercion spelling (avoiding any cross-spelling defeq)
  have h := (valuedAdicCompletion_eq_valuation
      (v := hq.toHeightOneSpectrumRingOfIntegersRat) (K := ℚ)
      ((q : NumberField.RingOfIntegers ℚ))).trans
    ((valuation_of_algebraMap
      (v := hq.toHeightOneSpectrumRingOfIntegersRat) (K := ℚ)
      ((q : NumberField.RingOfIntegers ℚ))).trans hval)
  convert h using 2
  norm_cast

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
    * `card_torsionBy_dvd_of_charP` (sorry node): over an
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
curve is cyclic** (sorry node, cut 2026-07-25 out of
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

WHY THIS IS STILL OPEN, and the only route visible from mathlib
(surveyed 2026-07-25). Mathlib has NO isogenies, no degree of a map of
curves, no separable/inseparable degree, no Frobenius on a Weierstrass
curve, no invariant differential, and no `Finite` instance for
`WeierstrassCurve.Affine.Point` — there is no `EllipticCurve/Isogeny`
file at all — so the argument above cannot be transcribed as it stands.
The reference project `~/cs/FLT` sorries even the characteristic-`0`
companion (`WeierstrassCurve.torsion_rank_two`), so there is nothing to
vendor either.

What mathlib DOES have is `Mathlib/AlgebraicGeometry/EllipticCurve/`
`DivisionPolynomial/`: `W.preΨ n`, `W.ΨSq n`, `W.Φ n`, with
`natDegree_preΨ'_le n : (W.preΨ' n).natDegree ≤ (n² - if Even n then 4
else 1) / 2` and `coeff_preΨ'` giving the coefficient in that degree as
`n` (up to the even correction); likewise `natDegree_ΨSq_le n :
(W.ΨSq n).natDegree ≤ n² - 1` with `coeff_ΨSq n : (W.ΨSq n).coeff
(n² - 1) = n²`. That last pair is the lever: in characteristic `p` the
leading coefficient `p²` VANISHES, which is the polynomial shadow of the
inseparability, and correspondingly `ΨSq_ne_zero` carries the hypothesis
`(n : R) ≠ 0` and does not apply. (By contrast `natDegree_Φ n = n²` and
`leadingCoeff_Φ n = 1` hold over ANY nontrivial ring — the degree `p²` of
`[p]` is still visible in characteristic `p`; it is only the *separable*
part that collapses.) The route is then three sub-atoms, none of which is
in mathlib:

* BRIDGE: for `P ≠ 0` and `n` odd, `(n : ℤ) • P = 0 ↔
  (Y.preΨ n).eval P.x = 0`. This is characteristic-free, is needed by the
  characteristic-`0` companion as well, and is the right thing to prove
  first — it is the only one of the three that is pure bookkeeping over
  the existing `DivisionPolynomial` API.
* NONVANISHING: `Y.preΨ p ≠ 0` in characteristic `p` (`ΨSq_ne_zero`
  needs `(n : R) ≠ 0`, so it gives nothing here).
* INSEPARABILITY: `Y.preΨ p` is a constant times a `p`-th power in
  `k[X]`. This is the deep one — it IS the inseparability of `[p]`.
  Given it, the count closes for odd `p`: `preΨ p` has at most
  `natDegree / p ≤ (p² - 1) / (2p) < p / 2` distinct roots, hence at most
  `(p - 1) / 2` `x`-coordinates; nonzero `p`-torsion points come in pairs
  `{P, -P}` with `P ≠ -P` (else `2P = 0 = pP` with `p` odd forces
  `P = 0`), so there are at most `p - 1` of them, i.e. `#Y(k)[p] ≤ p`,
  which with exponent `p` gives cyclicity.

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
  sorry

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
prime** (sorry node — the surviving local content of the ordinary
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

section TameCharacterOrbit

variable {Knum : Type*} [Field Knum] [NumberField Knum]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers Knum))

local notation "Kᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletion Knum v
local notation "𝒪ᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers Knum v
local notation "Lᵥ" =>
  AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion Knum v)
local notation "Rᵥ" =>
  IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers Knum v)
    (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion Knum v))

set_option backward.isDefEq.respectTransparency false in
/-- **Local inertia acts trivially on the `n`-th roots of unity when `n`
is prime to the residue characteristic** (PROVEN 2026-07-25). If `ζ ^ n = 1`
and the image of `n` avoids the maximal ideal of the big integral closure,
then every `σ ∈ localInertiaGroup v` fixes `ζ`: the ratio `σ ζ / ζ` is an
`n`-th root of unity congruent to `1` modulo the maximal ideal (because `σ`
is INERTIAL and `ζ` is a unit of the integral closure), hence is `1` by
`eq_one_of_pow_eq_one_of_sub_one_mem`.

The inertia hypothesis cannot be relaxed to the decomposition group: a
Frobenius lift moves `μ_n`. This is what makes the tame character
`σ ↦ σ ϖ / ϖ` below a group HOMOMORPHISM on inertia. -/
theorem localInertia_fixes_rootOfUnity {n : ℕ} (hn0 : n ≠ 0)
    (hn : ((n : ℕ) : Rᵥ) ∉ IsLocalRing.maximalIdeal Rᵥ)
    {ζ : Lᵥ} (hζ : ζ ^ n = 1)
    {σ : Lᵥ ≃ₐ[Kᵥ] Lᵥ} (hσ : σ ∈ localInertiaGroup v) :
    σ ζ = ζ := by
  classical
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, zero_pow hn0] at hζ
    exact zero_ne_one hζ
  have hroot : ∀ z : Lᵥ, z ^ n = 1 → IsIntegral 𝒪ᵥ z := by
    intro z hz
    refine ⟨Polynomial.X ^ n - 1, ?_, ?_⟩
    · have := Polynomial.monic_X_pow_sub_C (R := 𝒪ᵥ) (1 : 𝒪ᵥ) hn0
      simpa [Polynomial.C_1] using this
    · simp [Polynomial.eval₂_sub, hz]
  have hζinv : (ζ⁻¹) ^ n = 1 := by rw [inv_pow, hζ, inv_one]
  have hσζ : (σ ζ) ^ n = 1 := by rw [← map_pow, hζ, map_one]
  have hYpow : (σ ζ / ζ) ^ n = 1 := by rw [div_pow, hσζ, hζ, div_one]
  set Z : Rᵥ := ⟨ζ, hroot ζ hζ⟩ with hZdef
  set Zi : Rᵥ := ⟨ζ⁻¹, hroot _ hζinv⟩ with hZidef
  set Y : Rᵥ := ⟨σ ζ / ζ, hroot _ hYpow⟩ with hYdef
  have hinj : Function.Injective (algebraMap Rᵥ Lᵥ) := fun _ _ h => Subtype.ext h
  have hvZ : algebraMap _ _ Z = ζ := by rw [hZdef]; rfl
  have hvZi : algebraMap _ _ Zi = ζ⁻¹ := by rw [hZidef]; rfl
  have hvY : algebraMap _ _ Y = σ ζ / ζ := by rw [hYdef]; rfl
  have hvsZ : algebraMap _ _ (σ • Z) = σ ζ := by rw [hZdef]; rfl
  have hY1 : Y - 1 ∈ IsLocalRing.maximalIdeal Rᵥ := by
    have hmem : σ • Z - Z ∈ IsLocalRing.maximalIdeal Rᵥ := hσ Z
    have hEq : Y - 1 = (σ • Z - Z) * Zi := by
      apply hinj
      rw [map_sub, map_mul, map_sub, map_one, hvY, hvZ, hvZi, hvsZ]
      field_simp
    rw [hEq]
    exact Ideal.mul_mem_right _ _ hmem
  have hYn : Y ^ n = 1 := by
    apply hinj
    rw [map_pow, map_one, hvY]
    exact hYpow
  have hY0 : Y = 1 := eq_one_of_pow_eq_one_of_sub_one_mem hYn hY1 hn
  have hquot : σ ζ / ζ = 1 := by
    have h := congrArg (algebraMap Rᵥ Lᵥ) hY0
    rw [hvY, map_one] at h
    exact h
  have h3 : σ ζ / ζ * ζ = 1 * ζ := by rw [hquot]
  rwa [div_mul_cancel₀ _ hζ0, one_mul] at h3

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **Surjectivity of the tame character of local inertia, in ORBIT form,
over an arbitrary number field** (PROVEN 2026-07-25; this is the general
form of `exists_localInertia_tameCharacter_orbit` below). Let `π` generate
the maximal ideal of `𝒪ᵥ`, let `n` be prime to the residue characteristic
(in the form: the image of `n` avoids the maximal ideal of the big
integral closure), and let `ϖ ∈ Kᵥᵃˡᵍ` be ANY `n`-th root of `π`. Then some
`σ ∈ localInertiaGroup v` has `σ ^ k ϖ = ϖ → n ∣ k`.

PROOF (this replaces the Kummer-theory route recorded in the docstring
below; it needs neither `ℚ_p^nr`, nor Eisenstein irreducibility, nor the
Galois-group identification `Gal(K(a^{1/n})/K) ≃ μ_n` — the whole surjectivity
is extracted from the already-PROVEN
`maximalIdeal_map_eq_of_le_fixedField_localInertiaGroup`):

1. For any `σ` in the absolute Galois group, `ζ_σ := σ ϖ / ϖ` is an `n`-th
   root of unity, because `σ` fixes `π ∈ Kᵥ` and `ϖ ^ n = π`.
2. On INERTIA, `σ ↦ ζ_σ` is a group HOMOMORPHISM `F` into `(Kᵥᵃˡᵍ)ˣ`: this
   is exactly `localInertia_fixes_rootOfUnity` above, which says inertia
   acts trivially on `μ_n`.
3. `F.range` is contained in `μ_n`, hence finite, hence CYCLIC (a finite
   subgroup of the units of a domain). Let `d = #F.range`; then `d ∣ n`
   (a generator is an `n`-th root of unity) and `ζ_σ ^ d = 1` for every
   inertial `σ`, i.e. `ϖ ^ d` is fixed POINTWISE by `localInertiaGroup v`.
4. Hence `Kᵥ(ϖ ^ d)` lies in the fixed field of the local inertia, so
   `maximalIdeal_map_eq_of_le_fixedField_localInertiaGroup` makes `π` a
   GENERATOR of the maximal ideal of its integral closure `R`. But
   `α = ϖ ^ d` satisfies `α ^ m = π` with `m = n / d`, so `α ∈ 𝔪_R = (π)`,
   say `α = π β`, whence `π = π ^ m β ^ m` and `π` is a UNIT of `R` as soon
   as `m ≥ 2` — impossible in a local ring. Therefore `d = n`.
5. A generator of `F.range` is `F σ` for some inertial `σ`, and it has order
   exactly `n`; `σ ^ k ϖ = ζ_σ ^ k ϖ` then gives `ζ_σ ^ k = 1`, i.e. `n ∣ k`.

Step 3 is where the inertia quantifier is LOAD-BEARING twice over: once for
`F` to be a homomorphism at all, and once for step 4 to be about the fixed
field of INERTIA rather than of the decomposition group. -/
theorem exists_mem_localInertiaGroup_tameOrbit {n : ℕ} (hn0 : n ≠ 0)
    (hn : ((n : ℕ) : Rᵥ) ∉ IsLocalRing.maximalIdeal Rᵥ)
    (π : 𝒪ᵥ) (hπ : IsLocalRing.maximalIdeal 𝒪ᵥ = Ideal.span {π})
    (ϖ : Lᵥ) (hϖ : ϖ ^ n = algebraMap 𝒪ᵥ Lᵥ π) :
    ∃ σ : Lᵥ ≃ₐ[Kᵥ] Lᵥ, σ ∈ localInertiaGroup v ∧
      ∀ k : ℕ, (σ ^ k) ϖ = ϖ → n ∣ k := by
  classical
  -- `π ≠ 0`, hence `ϖ ≠ 0`
  have hπ0 : π ≠ 0 := by
    rintro rfl
    refine IsDiscreteValuationRing.not_a_field 𝒪ᵥ ?_
    rw [hπ, Ideal.span_singleton_eq_bot.mpr rfl]
  have hinjO : Function.Injective (algebraMap 𝒪ᵥ Lᵥ) := by
    rw [IsScalarTower.algebraMap_eq 𝒪ᵥ Kᵥ Lᵥ]
    exact (algebraMap Kᵥ Lᵥ).injective.comp fun _ _ h => Subtype.ext h
  have hπL : algebraMap 𝒪ᵥ Lᵥ π ≠ 0 := fun h => hπ0 (hinjO (by rw [h, map_zero]))
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, zero_pow hn0] at hϖ
    exact hπL hϖ.symm
  -- every automorphism multiplies `ϖ` by an `n`-th root of unity
  have hζpow : ∀ σ : Lᵥ ≃ₐ[Kᵥ] Lᵥ, (σ ϖ / ϖ) ^ n = 1 := by
    intro σ
    have hs : σ (algebraMap 𝒪ᵥ Lᵥ π) = algebraMap 𝒪ᵥ Lᵥ π := by
      rw [IsScalarTower.algebraMap_apply 𝒪ᵥ Kᵥ Lᵥ]
      exact σ.commutes _
    rw [div_pow, ← map_pow, hϖ, hs, ← hϖ, div_self (pow_ne_zero _ hϖ0)]
  have hζ0 : ∀ σ : Lᵥ ≃ₐ[Kᵥ] Lᵥ, σ ϖ / ϖ ≠ 0 := by
    intro σ h
    have hp := hζpow σ
    rw [h, zero_pow hn0] at hp
    exact zero_ne_one hp
  -- the inertia subgroup, read in the automorphism-group spelling
  let G : Subgroup (Lᵥ ≃ₐ[Kᵥ] Lᵥ) := localInertiaGroup v
  have hGmem : ∀ s : Lᵥ ≃ₐ[Kᵥ] Lᵥ, s ∈ G ↔ s ∈ localInertiaGroup v := fun _ => Iff.rfl
  have hfixζ : ∀ s ∈ G, ∀ t : Lᵥ ≃ₐ[Kᵥ] Lᵥ, s (t ϖ / ϖ) = t ϖ / ϖ := by
    intro s hs t
    exact localInertia_fixes_rootOfUnity v hn0 hn (hζpow t) ((hGmem s).mp hs)
  -- the tame character as a monoid homomorphism to the units
  let F : ↥G →* Lᵥˣ :=
    { toFun := fun s => Units.mk0 ((s : Lᵥ ≃ₐ[Kᵥ] Lᵥ) ϖ / ϖ) (hζ0 _)
      map_one' := by
        apply Units.ext
        show ((1 : ↥G) : Lᵥ ≃ₐ[Kᵥ] Lᵥ) ϖ / ϖ = 1
        rw [Subgroup.coe_one, AlgEquiv.one_apply, div_self hϖ0]
      map_mul' := by
        intro s t
        apply Units.ext
        show ((s * t : ↥G) : Lᵥ ≃ₐ[Kᵥ] Lᵥ) ϖ / ϖ =
          ((s : Lᵥ ≃ₐ[Kᵥ] Lᵥ) ϖ / ϖ) * ((t : Lᵥ ≃ₐ[Kᵥ] Lᵥ) ϖ / ϖ)
        rw [Subgroup.coe_mul, AlgEquiv.mul_apply]
        have ht : (t : Lᵥ ≃ₐ[Kᵥ] Lᵥ) ϖ = ((t : Lᵥ ≃ₐ[Kᵥ] Lᵥ) ϖ / ϖ) * ϖ :=
          (div_mul_cancel₀ _ hϖ0).symm
        rw [ht, map_mul, hfixζ _ s.2]
        field_simp }
  have hFval : ∀ s : ↥G, ((F s : Lᵥˣ) : Lᵥ) = (s : Lᵥ ≃ₐ[Kᵥ] Lᵥ) ϖ / ϖ := fun _ => rfl
  -- the image lands in the `n`-th roots of unity, hence is finite and cyclic
  have hFrange : F.range ≤ rootsOfUnity n Lᵥ := by
    intro u hu
    obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp hu
    rw [mem_rootsOfUnity', hFval]
    exact hζpow _
  haveI hnz : NeZero n := ⟨hn0⟩
  haveI hfin : Finite ↥(F.range) := by
    refine Finite.of_injective (β := ↥(rootsOfUnity n Lᵥ))
      (fun x => ⟨(x : Lᵥˣ), hFrange x.2⟩) ?_
    intro a b hab
    have hv : (a : Lᵥˣ) = (b : Lᵥˣ) :=
      congrArg (fun z : ↥(rootsOfUnity n Lᵥ) => (z : Lᵥˣ)) hab
    exact Subtype.ext hv
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(F.range))
  have hgcard : orderOf g = Nat.card ↥(F.range) :=
    orderOf_eq_card_of_forall_mem_zpowers hg
  set d : ℕ := Nat.card ↥(F.range) with hddef
  have hd0 : d ≠ 0 := Nat.card_pos.ne'
  have hgn' : (g : Lᵥˣ) ^ n = 1 := (mem_rootsOfUnity n _).mp (hFrange g.2)
  have hdn : d ∣ n := by
    rw [← hgcard, ← Subgroup.orderOf_coe]
    exact orderOf_dvd_of_pow_eq_one hgn'
  -- every tame character value is killed by `d`
  have hpowd : ∀ s : ↥G, ((F s : Lᵥˣ) : Lᵥ) ^ d = 1 := by
    intro s
    have h1 : (⟨F s, MonoidHom.mem_range.mpr ⟨s, rfl⟩⟩ : ↥(F.range)) ^ d = 1 :=
      pow_card_eq_one'
    have h2 := congrArg (fun x : ↥(F.range) => ((x : Lᵥˣ) : Lᵥ)) h1
    simpa using h2
  -- the iterated action of an inertia element on `ϖ`
  have hiter : ∀ (s : ↥G) (k : ℕ),
      (((s : Lᵥ ≃ₐ[Kᵥ] Lᵥ)) ^ k) ϖ = ((F s : Lᵥˣ) : Lᵥ) ^ k * ϖ := by
    intro s k
    have hsϖ : (s : Lᵥ ≃ₐ[Kᵥ] Lᵥ) ϖ = ((F s : Lᵥˣ) : Lᵥ) * ϖ := by
      rw [hFval]
      exact (div_mul_cancel₀ _ hϖ0).symm
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, hFval,
        hfixζ _ s.2, ← hFval, hsϖ]
      ring
  -- `d = n`: otherwise `ϖ ^ d` generates a ramified extension inside the
  -- fixed field of the inertia group
  have hdeq : d = n := by
    by_contra hne
    obtain ⟨m, hm⟩ := hdn
    have hm0 : m ≠ 0 := by rintro rfl; exact hn0 (by simpa using hm)
    have hm1 : m ≠ 1 := by rintro rfl; exact hne (by simpa using hm.symm)
    obtain ⟨t, ht⟩ : ∃ t, m = t + 2 := ⟨m - 2, by omega⟩
    set α : Lᵥ := ϖ ^ d with hαdef
    have hα : α ^ m = algebraMap 𝒪ᵥ Lᵥ π := by rw [hαdef, ← pow_mul, ← hm, hϖ]
    have hα0 : α ≠ 0 := pow_ne_zero _ hϖ0
    have hαfix : ∀ s : Lᵥ ≃ₐ[Kᵥ] Lᵥ, s ∈ localInertiaGroup v → s α = α := by
      intro s hs
      have hsG : s ∈ G := (hGmem s).mpr hs
      have hsϖ : s ϖ = ((F ⟨s, hsG⟩ : Lᵥˣ) : Lᵥ) * ϖ := by
        rw [hFval]
        exact (div_mul_cancel₀ _ hϖ0).symm
      rw [hαdef, map_pow, hsϖ, mul_pow, hpowd ⟨s, hsG⟩, one_mul]
    have hαint : IsIntegral Kᵥ α := Algebra.IsIntegral.isIntegral α
    haveI hfd : FiniteDimensional Kᵥ ↥(IntermediateField.adjoin Kᵥ {α}) :=
      IntermediateField.adjoin.finiteDimensional hαint
    have hMfix : IntermediateField.adjoin Kᵥ {α} ≤
        IntermediateField.fixedField (localInertiaGroup v) := by
      rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe,
        IntermediateField.mem_fixedField_iff]
      exact fun s hs => hαfix s hs
    have hmax := maximalIdeal_map_eq_of_le_fixedField_localInertiaGroup v
      (IntermediateField.adjoin Kᵥ {α}) hMfix
    have hspan : IsLocalRing.maximalIdeal
        (IntegralClosure 𝒪ᵥ ↥(IntermediateField.adjoin Kᵥ {α})) =
        Ideal.span {algebraMap 𝒪ᵥ
          (IntegralClosure 𝒪ᵥ ↥(IntermediateField.adjoin Kᵥ {α})) π} := by
      rw [← hmax, hπ, Ideal.map_span, Set.image_singleton]
    have hαmemM : α ∈ IntermediateField.adjoin Kᵥ {α} :=
      IntermediateField.mem_adjoin_simple_self Kᵥ α
    have hαMpow : (⟨α, hαmemM⟩ : ↥(IntermediateField.adjoin Kᵥ {α})) ^ m =
        algebraMap 𝒪ᵥ ↥(IntermediateField.adjoin Kᵥ {α}) π := by
      apply Subtype.ext
      rw [IntermediateField.coe_pow]
      exact hα
    have hαMint : IsIntegral 𝒪ᵥ (⟨α, hαmemM⟩ : ↥(IntermediateField.adjoin Kᵥ {α})) := by
      refine ⟨Polynomial.X ^ m - Polynomial.C π, Polynomial.monic_X_pow_sub_C π (by omega), ?_⟩
      simp [Polynomial.eval₂_sub, hαMpow]
    set a : IntegralClosure 𝒪ᵥ ↥(IntermediateField.adjoin Kᵥ {α}) :=
      ⟨⟨α, hαmemM⟩, hαMint⟩ with hadef
    set P : IntegralClosure 𝒪ᵥ ↥(IntermediateField.adjoin Kᵥ {α}) :=
      algebraMap 𝒪ᵥ _ π with hPdef
    have ha : a ^ m = P := by
      apply Subtype.ext
      rw [hadef, hPdef]
      exact hαMpow
    have hPmem : P ∈ IsLocalRing.maximalIdeal
        (IntegralClosure 𝒪ᵥ ↥(IntermediateField.adjoin Kᵥ {α})) := by
      rw [hspan, hPdef]
      exact Ideal.mem_span_singleton_self _
    have hPne : P ≠ 0 := by
      intro h
      apply hα0
      have hz : a ^ m = 0 := by rw [ha, h]
      have ha0 : a = 0 := pow_eq_zero_iff hm0 |>.mp hz
      have hc := congrArg (fun x : IntegralClosure 𝒪ᵥ ↥(IntermediateField.adjoin Kᵥ {α}) =>
        ((x.1 : ↥(IntermediateField.adjoin Kᵥ {α})) : Lᵥ)) ha0
      rw [hadef] at hc
      simpa using hc
    haveI hprime : (IsLocalRing.maximalIdeal
        (IntegralClosure 𝒪ᵥ ↥(IntermediateField.adjoin Kᵥ {α}))).IsPrime :=
      (IsLocalRing.maximalIdeal.isMaximal _).isPrime
    have hamem : a ∈ IsLocalRing.maximalIdeal
        (IntegralClosure 𝒪ᵥ ↥(IntermediateField.adjoin Kᵥ {α})) :=
      hprime.mem_of_pow_mem m (by rw [ha]; exact hPmem)
    rw [hspan, Ideal.mem_span_singleton] at hamem
    obtain ⟨b, hb⟩ := hamem
    have hunit : IsUnit P := by
      have h1 : P * (P ^ (t + 1) * b ^ m) = P * 1 := by
        rw [mul_one]
        calc P * (P ^ (t + 1) * b ^ m) = (P * b) ^ m := by rw [mul_pow, ht]; ring
          _ = a ^ m := by rw [← hb]
          _ = P := ha
      have h2 : P ^ (t + 1) * b ^ m = 1 := mul_left_cancel₀ hPne h1
      exact IsUnit.of_mul_eq_one (P ^ t * b ^ m) (by rw [← h2]; ring)
    exact ((IsLocalRing.mem_maximalIdeal _).mp hPmem) hunit
  -- the generator of the image is the value of some inertia element
  obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp g.2
  have hord : orderOf (F s) = n := by
    rw [hs, Subgroup.orderOf_coe, hgcard, hdeq]
  refine ⟨(s : Lᵥ ≃ₐ[Kᵥ] Lᵥ), (hGmem _).mp s.2, ?_⟩
  intro k hk
  rw [hiter s k] at hk
  have hζk : ((F s : Lᵥˣ) : Lᵥ) ^ k = 1 := by
    have h1 : ((F s : Lᵥˣ) : Lᵥ) ^ k * ϖ = 1 * ϖ := by rw [hk, one_mul]
    exact mul_right_cancel₀ hϖ0 h1
  have hFk : (F s) ^ k = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact hζk
  rw [← hord]
  exact orderOf_dvd_of_pow_eq_one hFk

end TameCharacterOrbit

open IsDedekindDomain in
/-- **Surjectivity of the tame character of local inertia, in ORBIT form**
(PROVEN 2026-07-25 by instantiating the general
`exists_mem_localInertiaGroup_tameOrbit` above at `K = ℚ`, `v = v_p` and
`π = p` — the uniformizer identification is
`maximalIdeal_adicCompletionIntegers_eq_span`, and the "prime to `p`" input
is `natCast_notMem_maximalIdeal_integralClosure`. Cut 2026-07-25 out of
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

HOW IT WAS ACTUALLY PROVED (2026-07-25). The Kummer/Eisenstein route above
was NOT needed, and neither of the two pieces recorded here as "missing
from mathlib" had to be built. See `exists_mem_localInertiaGroup_tameOrbit`
for the argument: the tame character is a homomorphism on inertia, its
image is a finite cyclic group `μ_d` with `d ∣ n`, and if `d < n` then
`ϖ ^ d` lies in the fixed field of the local inertia, which the PROVEN
`maximalIdeal_map_eq_of_le_fixedField_localInertiaGroup` says is
unramified — contradicting `(ϖ ^ d) ^ (n / d) = p`. So `d = n` and the
character is surjective. The pieces once listed here as prerequisites —
(a) *a totally ramified extension of local fields has the same residue
field*, and (b) *Kummer theory's identification `Gal(K(a^{1/n})/K) ≃ μ_n`*
— remain absent from mathlib, but this node no longer needs either: the
whole ramification input is supplied by the already-proven fixed-field
theorem. -/
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
        n ∣ k := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hpn (dvd_zero p)
  obtain ⟨σ, hσ, hk⟩ := exists_mem_localInertiaGroup_tameOrbit
    hp.toHeightOneSpectrumRingOfIntegersRat hn0
    (natCast_notMem_maximalIdeal_integralClosure hp hpn)
    ((p : ℕ) : HeightOneSpectrum.adicCompletionIntegers ℚ
      hp.toHeightOneSpectrumRingOfIntegersRat)
    (maximalIdeal_adicCompletionIntegers_eq_span hp) ϖ
    (by rw [map_natCast]; exact hϖ)
  exact ⟨σ, hσ, hk⟩

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
* `WeierstrassCurve.exists_quotient_isogeny_of_odd_prime_card` (sorry
  node) — the true Vélu core, cut at the literature statement: the
  quotient by a Galois-stable CYCLIC subgroup of ODD prime order
  (Vélu 1971; Silverman AEC III.4.12).
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

/-- **Normal form for a rational `2`-torsion point** (sorry node, cut
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
`2`-isogeny** (sorry node, cut out of
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

/-- **The odd-prime-order quotient-isogeny leaf — Vélu's construction**
(sorry node, sharpened 2026-07-23 from the general prime-order
statement by splitting off the rational `2`-isogeny case): for a
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

**Route audit (2026-07-25).** This node did NOT decompose further at
this level: unlike the `2`-isogeny case — now split into a
normalisation brick and a normal-form-formula brick — the odd case has
no coordinate normalisation to hide behind (the points of `C` are not
individually rational), so every honest cut still has to produce the
quotient curve and the map together, i.e. it remains a single
construction. The recommended shape for a dedicated attack, in its own
module (say `Fermat/FLT/EllipticCurve/Velu.lean`), over an arbitrary
base field and an arbitrary finite subgroup, is:

1. Choose a `Finset S` of representatives of `C \ {0}` modulo `±`
   (`(ℓ − 1)/2` points, `ℓ` odd, so no point of order `2` occurs).
2. For `Q = (x_Q, y_Q) ∈ S` set, following Vélu 1971 (p. 238; see also
   Kohel's thesis §2.4, which transcribes them in this normalisation),
   `gˣ_Q = 3x_Q² + 2a₂x_Q + a₄ − a₁y_Q`,
   `gʸ_Q = −2y_Q − a₁x_Q − a₃`, `t_Q = 2gˣ_Q − a₁gʸ_Q`,
   `u_Q = (gʸ_Q)²`, `w_Q = u_Q + t_Q x_Q`, and
   `t = Σ_{Q ∈ S} t_Q`, `w = Σ_{Q ∈ S} w_Q`.
3. The quotient curve is
   `E' : y² + a₁xy + a₃y = x³ + a₂x² + (a₄ − 5t)x
        + (a₆ − (a₁² + 4a₂)t − 7w)`,
   and the isogeny is `x' = x + Σ_Q [t_Q/(x − x_Q) + u_Q/(x − x_Q)²]`
   with the matching expression for `y'` (transcribe it from the
   source; it is the `x`-derivative combination
   `y' = y − Σ_Q [2u_Q(y + …)/(x − x_Q)³ + …]`).
4. First sub-brick, and the natural entry point: `t, w ∈ ℚ` — each
   summand is invariant under `Q ↦ −Q` and Galois permutes `C`, hence
   permutes `S` up to sign, so the sums are Galois-fixed and descend by
   `InfiniteGalois.mem_range_algebraMap_iff_fixed` (the scalar analogue
   of `exists_point_eq_baseChange_of_fixed` above).
5. The remaining bricks are the geometry: `E'.IsElliptic`, the
   well-definedness (nonsingularity of the image point), ADDITIVITY,
   and the kernel. Additivity by direct coordinate algebra is
   prohibitive; the standard route is the function-field one — `φ`
   corresponds to the inclusion of the `C`-invariant subfield of
   `W.FunctionField` (mathlib's `WeierstrassCurve.Affine.FunctionField`
   is available), under which additivity is inherited from the
   translation action rather than computed. -/
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
      (∀ Pt : (E⁄(AlgebraicClosure ℚ)).Point, φ Pt = 0 ↔ Pt ∈ C) :=
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- **The prime-order quotient isogeny** (DERIVED 2026-07-23 from the
rational `2`-isogeny leaf `exists_quotient_isogeny_of_rational_two_torsion`
and the odd-order Vélu leaf `exists_quotient_isogeny_of_odd_prime_card`):
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

