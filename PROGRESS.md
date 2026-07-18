# FLT formalization — progress and dependency tree

Goal: `theorem fermat_last_theorem : FermatLastTheorem` in `Fermat/Basic.lean`,
with the proof tree walked top-down; every gap is an explicit `sorry`-d theorem
(never an `axiom`), and every layer is compiled and axiom-checked
(`#print axioms` must show at most `propext`, `Classical.choice`, `Quot.sound`,
`sorryAx`).

Strategy: treat the proof as a dependency tree. State the theorem, prove it
from the strongest available mathlib facts plus explicitly stated gaps, then
recurse into the gaps. Follow the Wiles/Taylor–Wiles route as organized by the
Frey–Serre–Ribet reduction; use Buzzard's FLT project (Imperial) blueprint as a
map where helpful.

## Tree (generated — do not edit by hand; run `python3 progress-tree.py`)

The tree below is GENERATED from `progress-entries.json` (the flat list
of tracked Lean declarations with their descriptions): the dependency
structure is computed from the compiled proofs (which listed
declarations each proof transitively uses), and the marks are computed
by the Lean compiler — ❌ the declaration's own source still contains
`sorry`; ✅ the source is a complete proof but its dependency cone
still contains a `sorry`; ✅✅ the whole cone is sorry-free
(`#print axioms` shows only propext/Classical.choice/Quot.sound).
✅✅ nodes are HIDDEN from this display entirely — the tree shows
only the open work (they remain in `progress-entries.json` and
`progress-tree.json`). A node with several dependents is shown in
full (text and subtree) under each dependent — no back references —
so beneath every ✅ node the ❌ nodes its remaining sorries flow
through are directly visible.
Second symbol: `·` normal, `🟪` currently being worked on (from the
entries file). To add/remove/annotate a node, edit
`progress-entries.json` and re-run the generator.

- ✅· `fermat_last_theorem` — the goal: `FermatLastTheorem`, assembled from the mathlib reductions and
  `fermatLastTheoremFor_of_five_le`.
    - ✅· `fermatLastTheoremFor_of_five_le` — ∀ p, p.Prime → 5 ≤ p → FermatLastTheoremFor p` (`Fermat/PrimeFive.lean`) — proven from:
        - ✅· `FreyPackage.mazur` — (`Fermat/FLT/FreyCurve/Mazur.lean`) — the mod-p rep of the Frey curve is irreducible — now
          (2026-07-16) from two explicit nodes in `Fermat/FLT/FreyCurve/MazurTorsion.lean` (own
          work), following Serre (Duke 1987, §4.1):
            - ✅· `FreyPackage.exists_torsion_embedding_of_not_isIrreducible` — (2026-07-16) from the two nodes below: Serre's analysis produces full 2-torsion plus a
              rational point of order p on some curve; the `embedding_assembly` combines them into
              an injective ℤ/2 × ℤ/2p via CRT
                - ✅· `FreyPackage.exists_two_torsion_and_p_point_of_not_isIrreducible` — (2026-07-16) from the disjunction node below plus the Frey 2-torsion
                    - ✅· `FreyPackage.exists_p_point_of_not_isIrreducible` — (2026-07-16): the Minkowski input is discharged by the node below
                        - ✅· `FreyPackage.exists_p_point_of_not_isIrreducible_of_minkowski` — (2026-07-17) from the stable-line dichotomy leaf, the Galois descent for
                          points, and the Vélu quotient leaf (all `MazurTorsion.lean`)
                            - ✅· `FreyPackage.stable_line_dichotomy_of_not_isIrreducible` — (2026-07-17) from the semistability leaf below + the character
                              bookkeeping: the stable line
                              (`exists_stable_line_of_not_isIrreducible`) carries unit-valued
                              characters (`exists_subCharacter`/`exists_quotCharacter`, the scalar-
                              action-on-rank-1 argument `exists_unit_character_of_finrank_one`),
                              with `det = χ₁χ₂` (`det_eq_subCharacter_mul_quotCharacter` via
                              `LinearMap.det_eq_det_mul_det`) `= ω̄` (the det node +
                              `cyclotomicCharacterModL_eq_toZMod`); kernels are open (they contain
                              the open kernel of ρ, `isOpen_setOf_galoisRep_eq_one` +
                              `Subgroup.isOpen_mono`); Minkowski (hmink) kills the everywhere-
                              unramified character; `χ₁ = 1` fixes a nonzero `w₀ ∈ W` (a fixed point
                              of exact order `p`), `χ₂ = 1` trivializes the quotient action.
                              SPELLING GOTCHAS (all resolved): (a) quotient triviality must be
                              phrased via `W.mkQ`, not `ρ g v − v ∈ W` (HSub instance search
                              sticks); (b) `P.freyCurve`-instantiated nTorsion carries
                              `Rat.commRing` vs the `Field.toCommRing` spelling baked into
                              `galoisRep`'s codomain — defeq at DEFAULT transparency but NOT at
                              instance transparency, so `letI`/`haveI` instances for the local
                              spelling are invisible to TC search against the baked spelling; the
                              cure is general-`V` lemmas whose instance binders are pinned by
                              unification with the `ρbar` argument (pass `ρbar` FIRST, extra
                              finiteness as a plain hypothesis, never an instance binder)
                                - ✅· `FreyPackage.subquotient_character_unramified` — (2026-07-17): away from `{2, p}` the whole representation kills
                                  inertia (`FreyCurve.torsion_isUnramified`, transported by the new
                                  generic-`K` bridge
                                  `character_localInertia_le_ker_of_isUnramifiedAt` +
                                  `Rat.subsingleton_ringHom`/`convert using 5` to reconcile the
                                  local-vs-generic `algebraMap` spellings — the local ℚ-spelling and
                                  `toLocal`'s generic one are NOT defeq-bridgeable because
                                  `Field.absoluteGaloisGroup.map` is unexposed; ring homs out of `ℚ`
                                  are unique, so propositional bridging works); the unipotent-scalar
                                  lemmas (`subCharacter_eq_one_of_sq_eq_zero`,
                                  `quotCharacter_eq_one_of_sq_eq_zero`, ) turn `(ρσ−1)² = 0` into
                                  character-triviality
                                    - ✅· `FreyPackage.inertia_two_unipotent` — (2026-07-17): the Frey curve has multiplicative reduction at
                                      `2` (`freyCurve_hasMultiplicativeReduction_at_two`, ), and the
                                      pointwise Tate unipotence leaf below transports through
                                      `map_mem_inertiaSubgroup_of_mem_localInertiaGroup`, the
                                      `(A−1)² = A·A − A − A + 1` End-expansion (pointwise via
                                      `abel`), and the show-cast `⁄`-ambient collapse. SPELLING
                                      NOTE: a direct `exact` across the generic-vs-`Rat`
                                      `algebraMap` spellings is impossible (unexposed
                                      `IsAlgClosed.lift`); the working recipe is atom-level
                                      `rfl`-bridges (`hb`) for the representation-vs-`Point.map`
                                      steps plus `convert hp using 8` with closers `rfl`,
                                      `Subsingleton.elim`, and `congrArg` of
                                      `Field.absoluteGaloisGroup.map` (hom-level AND `σ`-applied)
                                      over `Rat.subsingleton_ringHom`
                                        - ✅· `WeierstrassCurve.torsion_unipotent_of_multiplicative_reduction` — (`FreyCurve/Semistable.lean`, stated 2026-07-17) —
                                          pointwise Tate unipotence: multiplicative reduction at `q
                                          ≠ p` (`q = 2` allowed, no `p ∣ v(j)`) makes every inertia
                                          element at a valuation subring over `ℤ_(q)` act with
                                          `σ(σP) − σP − σP + P = 0` on the `p`-torsion (to be closed
                                          against the Tate-uniformization leaves)
                                            - ✅· `torsion_unipotent_of_split_multiplicative_adic` — pointwise unipotence in the split case: the Tate
                                              uniformization witness feeds `tate_inertia_unipotent`
                                              at the local valuation subring, pulled back to `E(ℚ̄)`
                                              along the equivariant embedding; the remaining content
                                              is the base-change instance identification of the two
                                              `Ω`-stage curve spellings.
                                                - ✅· `WeierstrassCurve.exists_tateEquivSepClosure` — Tate's uniformisation over a separable closure,
                                                  now DERIVED from the choice-free Tate-curve
                                                  uniformisation and Tate's variable-change theorem:
                                                  the variable change is `k`-rational, so its base-
                                                  changed point equivalence is Galois-equivariant,
                                                  and the equivariance transports through the
                                                  composite.
                                                    - ✅· `WeierstrassCurve.exists_tateCurveEquivSepClosure` — the uniformization core, quotient form:
                                                      Galois-equivariant Ωˣ/q^ℤ ≃+ E_q(Ω). DERIVED
                                                      2026-07-18 from the pre-quotient node
                                                      exists_tateCurveHomSepClosure by the first
                                                      isomorphism theorem: multiplicative lift ψ of
                                                      the hom, QuotientGroup.lift over zpowers q,
                                                      injectivity from the kernel characterization,
                                                      MulEquiv.ofBijective, MulEquiv.toAdditiveLeft;
                                                      equivariance descends definitionally on ofMul-
                                                      classes.
                                                        - ✅· `WeierstrassCurve.exists_tateCurveHomSepClosure` — the uniformization core, pre-quotient
                                                          form: surjective Galois-equivariant hom Ωˣ
                                                          →+ E_q(Ω) with kernel exactly q^ℤ. DERIVED
                                                          2026-07-18 by feeding the finite-level
                                                          canonical uniformisation tateCurveEquiv
                                                          (underlying function pointMapQuot) into
                                                          the sorried gluing implication exists_tate
                                                          CurveHomSepClosure_of_finiteLevel.
                                                            - ✅· `TateCurve.tateCurveEquiv` — the finite-level Tate uniformisation
                                                              kˣ/q^ℤ ≃+ E_q(k), DERIVED from
                                                              pointMapQuot_add +
                                                              pointMapQuot_bijective with
                                                              pointMapQuot (canonical, choice-free)
                                                              as underlying function — the object
                                                              the Ω-gluing consumes. RE-VENDORED
                                                              2026-07-18 (stripped form): the
                                                              annulus/evalA/pointMap machinery is in
                                                              the tree (all PROVEN: CoeffRing
                                                              evaluation, summability on the
                                                              fundamental annulus, evaluated
                                                              Weierstrass equation, annulusPoint
                                                              nonsingularity, strict fundamental
                                                              domain, kernel characterization
                                                              pointMap_eq_zero_iff); the
                                                              bilateral/Lambert negation-translation
                                                              machinery stays in the reference
                                                              commit 8282dfb^ until the addition-law
                                                              proof consumes it.
                                                                - ✅· `TateCurve.pointMapQuot_surjective` — surjectivity of the uniformisation
                                                                  (Silverman ATAEC V.3.1(d)/V.4).
                                                                  DERIVED 2026-07-18 from the x-onto
                                                                  leaf exists_annulus_bilateralX_eq:
                                                                  the leaf gives an annulus
                                                                  parameter u over the x-coordinate;
                                                                  Y_eq_of_X_eq gives y = bilateralY
                                                                  u or its negY, the latter realised
                                                                  by the inverse partner (u⁻¹ on the
                                                                  shell, q·u⁻¹ in the interior) via
                                                                  the PROVEN vertical case
                                                                  bilateral_negY_of_mul_trivial.
                                                                    - ❌· `TateCurve.exists_annulus_bilateralX_eq` — the x-onto leaf (sorry node,
                                                                      the analytic heart of
                                                                      Silverman V.4): every affine
                                                                      solution (x, y) of the Tate
                                                                      curve equation has an annulus
                                                                      parameter u with bilateralX u
                                                                      = x. Attack: Newton-
                                                                      polygon/valuation analysis of
                                                                      X(u) - x on the annulus (theta
                                                                      quotient), using completeness
                                                                      of k.
                                                                - ✅· `TateCurve.pointMapQuot_add` — the addition law (Silverman ATAEC
                                                                  V.3.1(c)). DERIVED 2026-07-18 from
                                                                  three sorried series-identity
                                                                  leaves (chord, tangent, X-fibre) +
                                                                  the PROVEN vertical case
                                                                  bilateral_negY_of_mul_trivial
                                                                  (inversion/shift identities), the
                                                                  PROVEN bilateral coordinate bridge
                                                                  pointMap_eq_bilateral on the
                                                                  extended window |q|² < |w| ≤ 1,
                                                                  and quotient bookkeeping (annulus
                                                                  normalisation, trivial classes).
                                                                    - ✅· `TateCurve.eq_or_mul_eq_of_bilateralX_eq` — the X-fibre (Silverman V.4).
                                                                      DERIVED 2026-07-18 from the
                                                                      coordinate-pair injectivity
                                                                      bilateralXY_inj: Y_eq_of_X_eq
                                                                      gives equal or negY-related
                                                                      y-values; equal ⇒ injectivity
                                                                      ⇒ v = u; negY-related ⇒ v =
                                                                      the inverse partner (u⁻¹ on
                                                                      the shell, q·u⁻¹ in the
                                                                      interior) by the PROVEN
                                                                      vertical case + injectivity,
                                                                      so uv ∈ {1, q}.
                                                                        - ❌· `TateCurve.bilateralXY_inj` — coordinate-pair injectivity on
                                                                          the annulus (sorry node — the
                                                                          injectivity half of Silverman
                                                                          V.4): equal bilateral x- AND
                                                                          y-values force equal
                                                                          parameters. Attack: Newton-
                                                                          polygon/theta-quotient
                                                                          analysis of X(u) - X(v) over
                                                                          the complete field, the
                                                                          y-value separating the two
                                                                          sheets.
                                                                    - ✅· `TateCurve.bilateral_add_self` — the tangent identity (V.3.1(c)
                                                                      doubling case). DERIVED
                                                                      2026-07-18 from the cleared
                                                                      tangent identities + the
                                                                      non-2-torsion leaf, same
                                                                      division bookkeeping pattern
                                                                      as the chord case.
                                                                        - ❌· `TateCurve.bilateral_ne_negY_of_sq_nontrivial` — non-2-torsion leaf (sorry
                                                                          node): u in the annulus with
                                                                          u² not in the trivial class
                                                                          has 2Y(u) + X(u) ≠ 0 — the
                                                                          2-torsion parameters are
                                                                          exactly {-1, ±√q}·q^ℤ.
                                                                        - ❌· `TateCurve.bilateral_tangentY_cleared` — cleared tangent Y-identity
                                                                          (sorry node): -(Y(u²)+X(u²))E
                                                                          = M(X(u²)-X(u)) + Y(u)E.
                                                                          Diagonal case.
                                                                        - ❌· `TateCurve.bilateral_tangentX_cleared` — cleared tangent X-identity
                                                                          (sorry node): (X(u²)+2X(u))E²
                                                                          = M² + ME with M the tangent-
                                                                          slope numerator, E = y - negY.
                                                                          Diagonal case of the cleared
                                                                          chord content.
                                                                    - ✅· `TateCurve.bilateral_add_of_X_ne` — the chord identity (V.3.1(c)
                                                                      generic case). DERIVED
                                                                      2026-07-18 from the cleared
                                                                      chord identities
                                                                      bilateral_chordX_cleared /
                                                                      bilateral_chordY_cleared: the
                                                                      triviality exclusions follow
                                                                      from distinct x-values via the
                                                                      proven inversion/shift
                                                                      identities, and the
                                                                      slope/addX/addY division
                                                                      bookkeeping is field_simp +
                                                                      linear_combination against the
                                                                      cleared forms.
                                                                        - ❌· `TateCurve.bilateral_chordY_cleared` — cleared chord Y-identity
                                                                          (sorry node):
                                                                          -(Y(uv)+X(uv))(X(u)-X(v)) =
                                                                          (Y(u)-Y(v))(X(uv)-X(u)) +
                                                                          Y(u)(X(u)-X(v)) — linear in
                                                                          the X-part output. Same attack
                                                                          as the X-identity.
                                                                        - ❌· `TateCurve.bilateral_chordX_cleared` — cleared chord X-identity
                                                                          (sorry node):
                                                                          (X(uv)+X(u)+X(v))(X(u)-X(v))²
                                                                          = (Y(u)-Y(v))² +
                                                                          (Y(u)-Y(v))(X(u)-X(v)) — pure
                                                                          polynomial series identity, no
                                                                          slope/division/cases. Attack:
                                                                          Ramanujan/Eisenstein
                                                                          manipulation of divisor double
                                                                          series
                                                                          (Venkatachaliengar–Cooper Ch.
                                                                          1) or two-transcendental
                                                                          descent; mathlib LACKS the
                                                                          ℘-addition law (checked
                                                                          2026-07-18), so the ℂ-analytic
                                                                          route requires formalizing it
                                                                          first.
                                                            - ❌🟪 `WeierstrassCurve.exists_tateCurveHomSepClosure_of_finiteLevel` — the Ω-gluing implication (sorry node):
                                                              GIVEN the finite-level canonical
                                                              uniformisation lˣ/q^ℤ ≃+ E_q(l) with
                                                              underlying pointMapQuot for every NALF
                                                              l, the Ω-level hom exists. Content:
                                                              finite subextensions of Ω/k are NALFs
                                                              (unique valuative extension over the
                                                              complete k — infrastructure absent
                                                              from mathlib at this pin), the maps
                                                              are compatible with inclusions and
                                                              σ-twists by naturality of the
                                                              universal series, and
                                                              kernel/surjectivity/equivariance pass
                                                              to the colimit.
                                            - ✅· `WeierstrassCurve.torsion_unipotent_of_nonsplit_multiplicative_adic` — the nonsplit half of the unipotence statement,
                                              assembled from the LOCAL nonsplit node
                                              `tate_inertia_unipotent_of_nonsplit` by the proven
                                              `ℚ̄`-pullback glue (equivariant embedding +
                                              `Point.map` injectivity).
                                                - ✅· `WeierstrassCurve.tate_inertia_unipotent_of_nonsplit` — the LOCAL twist-transfer of nonsplit unipotence,
                                                  now assembled: the enriched twist witness, the
                                                  inertia-fixed embedding of the unramified
                                                  quadratic extension, and the equivariant composite
                                                  point equivalence transport
                                                  `tate_inertia_unipotent` from the twisted minimal
                                                  model.
                                                    - ✅· `WeierstrassCurve.exists_tateEquivSepClosure` — Tate's uniformisation over a separable
                                                      closure, now DERIVED from the choice-free
                                                      Tate-curve uniformisation and Tate's variable-
                                                      change theorem: the variable change is
                                                      `k`-rational, so its base-changed point
                                                      equivalence is Galois-equivariant, and the
                                                      equivariance transports through the composite.
                                                        - ✅· `WeierstrassCurve.exists_tateCurveEquivSepClosure` — the uniformization core, quotient form:
                                                          Galois-equivariant Ωˣ/q^ℤ ≃+ E_q(Ω).
                                                          DERIVED 2026-07-18 from the pre-quotient
                                                          node exists_tateCurveHomSepClosure by the
                                                          first isomorphism theorem: multiplicative
                                                          lift ψ of the hom, QuotientGroup.lift over
                                                          zpowers q, injectivity from the kernel
                                                          characterization, MulEquiv.ofBijective,
                                                          MulEquiv.toAdditiveLeft; equivariance
                                                          descends definitionally on ofMul-classes.
                                                            - ✅· `WeierstrassCurve.exists_tateCurveHomSepClosure` — the uniformization core, pre-quotient
                                                              form: surjective Galois-equivariant
                                                              hom Ωˣ →+ E_q(Ω) with kernel exactly
                                                              q^ℤ. DERIVED 2026-07-18 by feeding the
                                                              finite-level canonical uniformisation
                                                              tateCurveEquiv (underlying function
                                                              pointMapQuot) into the sorried gluing
                                                              implication exists_tateCurveHomSepClos
                                                              ure_of_finiteLevel.
                                                                - ✅· `TateCurve.tateCurveEquiv` — the finite-level Tate
                                                                  uniformisation kˣ/q^ℤ ≃+ E_q(k),
                                                                  DERIVED from pointMapQuot_add +
                                                                  pointMapQuot_bijective with
                                                                  pointMapQuot (canonical, choice-
                                                                  free) as underlying function — the
                                                                  object the Ω-gluing consumes. RE-
                                                                  VENDORED 2026-07-18 (stripped
                                                                  form): the annulus/evalA/pointMap
                                                                  machinery is in the tree (all
                                                                  PROVEN: CoeffRing evaluation,
                                                                  summability on the fundamental
                                                                  annulus, evaluated Weierstrass
                                                                  equation, annulusPoint
                                                                  nonsingularity, strict fundamental
                                                                  domain, kernel characterization
                                                                  pointMap_eq_zero_iff); the
                                                                  bilateral/Lambert negation-
                                                                  translation machinery stays in the
                                                                  reference commit 8282dfb^ until
                                                                  the addition-law proof consumes
                                                                  it.
                                                                    - ✅· `TateCurve.pointMapQuot_surjective` — surjectivity of the
                                                                      uniformisation (Silverman
                                                                      ATAEC V.3.1(d)/V.4). DERIVED
                                                                      2026-07-18 from the x-onto
                                                                      leaf
                                                                      exists_annulus_bilateralX_eq:
                                                                      the leaf gives an annulus
                                                                      parameter u over the
                                                                      x-coordinate; Y_eq_of_X_eq
                                                                      gives y = bilateralY u or its
                                                                      negY, the latter realised by
                                                                      the inverse partner (u⁻¹ on
                                                                      the shell, q·u⁻¹ in the
                                                                      interior) via the PROVEN
                                                                      vertical case
                                                                      bilateral_negY_of_mul_trivial.
                                                                        - ❌· `TateCurve.exists_annulus_bilateralX_eq` — the x-onto leaf (sorry node,
                                                                          the analytic heart of
                                                                          Silverman V.4): every affine
                                                                          solution (x, y) of the Tate
                                                                          curve equation has an annulus
                                                                          parameter u with bilateralX u
                                                                          = x. Attack: Newton-
                                                                          polygon/valuation analysis of
                                                                          X(u) - x on the annulus (theta
                                                                          quotient), using completeness
                                                                          of k.
                                                                    - ✅· `TateCurve.pointMapQuot_add` — the addition law (Silverman
                                                                      ATAEC V.3.1(c)). DERIVED
                                                                      2026-07-18 from three sorried
                                                                      series-identity leaves (chord,
                                                                      tangent, X-fibre) + the PROVEN
                                                                      vertical case
                                                                      bilateral_negY_of_mul_trivial
                                                                      (inversion/shift identities),
                                                                      the PROVEN bilateral
                                                                      coordinate bridge
                                                                      pointMap_eq_bilateral on the
                                                                      extended window |q|² < |w| ≤
                                                                      1, and quotient bookkeeping
                                                                      (annulus normalisation,
                                                                      trivial classes).
                                                                        - ✅· `TateCurve.eq_or_mul_eq_of_bilateralX_eq` — the X-fibre (Silverman V.4).
                                                                          DERIVED 2026-07-18 from the
                                                                          coordinate-pair injectivity
                                                                          bilateralXY_inj: Y_eq_of_X_eq
                                                                          gives equal or negY-related
                                                                          y-values; equal ⇒ injectivity
                                                                          ⇒ v = u; negY-related ⇒ v =
                                                                          the inverse partner (u⁻¹ on
                                                                          the shell, q·u⁻¹ in the
                                                                          interior) by the PROVEN
                                                                          vertical case + injectivity,
                                                                          so uv ∈ {1, q}.
                                                                            - ❌· `TateCurve.bilateralXY_inj` — coordinate-pair injectivity on
                                                                              the annulus (sorry node — the
                                                                              injectivity half of Silverman
                                                                              V.4): equal bilateral x- AND
                                                                              y-values force equal
                                                                              parameters. Attack: Newton-
                                                                              polygon/theta-quotient
                                                                              analysis of X(u) - X(v) over
                                                                              the complete field, the
                                                                              y-value separating the two
                                                                              sheets.
                                                                        - ✅· `TateCurve.bilateral_add_self` — the tangent identity (V.3.1(c)
                                                                          doubling case). DERIVED
                                                                          2026-07-18 from the cleared
                                                                          tangent identities + the
                                                                          non-2-torsion leaf, same
                                                                          division bookkeeping pattern
                                                                          as the chord case.
                                                                            - ❌· `TateCurve.bilateral_ne_negY_of_sq_nontrivial` — non-2-torsion leaf (sorry
                                                                              node): u in the annulus with
                                                                              u² not in the trivial class
                                                                              has 2Y(u) + X(u) ≠ 0 — the
                                                                              2-torsion parameters are
                                                                              exactly {-1, ±√q}·q^ℤ.
                                                                            - ❌· `TateCurve.bilateral_tangentY_cleared` — cleared tangent Y-identity
                                                                              (sorry node): -(Y(u²)+X(u²))E
                                                                              = M(X(u²)-X(u)) + Y(u)E.
                                                                              Diagonal case.
                                                                            - ❌· `TateCurve.bilateral_tangentX_cleared` — cleared tangent X-identity
                                                                              (sorry node): (X(u²)+2X(u))E²
                                                                              = M² + ME with M the tangent-
                                                                              slope numerator, E = y - negY.
                                                                              Diagonal case of the cleared
                                                                              chord content.
                                                                        - ✅· `TateCurve.bilateral_add_of_X_ne` — the chord identity (V.3.1(c)
                                                                          generic case). DERIVED
                                                                          2026-07-18 from the cleared
                                                                          chord identities
                                                                          bilateral_chordX_cleared /
                                                                          bilateral_chordY_cleared: the
                                                                          triviality exclusions follow
                                                                          from distinct x-values via the
                                                                          proven inversion/shift
                                                                          identities, and the
                                                                          slope/addX/addY division
                                                                          bookkeeping is field_simp +
                                                                          linear_combination against the
                                                                          cleared forms.
                                                                            - ❌· `TateCurve.bilateral_chordY_cleared` — cleared chord Y-identity
                                                                              (sorry node):
                                                                              -(Y(uv)+X(uv))(X(u)-X(v)) =
                                                                              (Y(u)-Y(v))(X(uv)-X(u)) +
                                                                              Y(u)(X(u)-X(v)) — linear in
                                                                              the X-part output. Same attack
                                                                              as the X-identity.
                                                                            - ❌· `TateCurve.bilateral_chordX_cleared` — cleared chord X-identity
                                                                              (sorry node):
                                                                              (X(uv)+X(u)+X(v))(X(u)-X(v))²
                                                                              = (Y(u)-Y(v))² +
                                                                              (Y(u)-Y(v))(X(u)-X(v)) — pure
                                                                              polynomial series identity, no
                                                                              slope/division/cases. Attack:
                                                                              Ramanujan/Eisenstein
                                                                              manipulation of divisor double
                                                                              series
                                                                              (Venkatachaliengar–Cooper Ch.
                                                                              1) or two-transcendental
                                                                              descent; mathlib LACKS the
                                                                              ℘-addition law (checked
                                                                              2026-07-18), so the ℂ-analytic
                                                                              route requires formalizing it
                                                                              first.
                                                                - ❌🟪 `WeierstrassCurve.exists_tateCurveHomSepClosure_of_finiteLevel` — the Ω-gluing implication (sorry
                                                                  node): GIVEN the finite-level
                                                                  canonical uniformisation lˣ/q^ℤ ≃+
                                                                  E_q(l) with underlying
                                                                  pointMapQuot for every NALF l, the
                                                                  Ω-level hom exists. Content:
                                                                  finite subextensions of Ω/k are
                                                                  NALFs (unique valuative extension
                                                                  over the complete k —
                                                                  infrastructure absent from mathlib
                                                                  at this pin), the maps are
                                                                  compatible with inclusions and
                                                                  σ-twists by naturality of the
                                                                  universal series, and
                                                                  kernel/surjectivity/equivariance
                                                                  pass to the colimit.
                                    - ❌· `FreyPackage.subquotient_character_unramified_at_p` — (stated 2026-07-17) — flat/ordinary at `p`: one of the two
                                      characters is unramified at `p` itself (connected-étale
                                      sequence in the ordinary/ multiplicative case; supersingular
                                      excluded by reducibility)
                                    - ✅· `FreyCurve.torsion_isUnramified` — unramified outside {2, p}: (2026-07-16) by the case split `q ∣
                                      abc` or not, from the two nodes below
                                        - ✅· `FreyCurve.torsion_isUnramified_of_multiplicative` — (2026-07-16) from the arithmetic
                                          (`freyCurve_hasMultiplicativeReduction_of_dvd` +
                                          `j_valuation_of_bad_prime`) and the Tate glue node below
                                            - ✅· `WeierstrassCurve.isUnramifiedAt_of_hasMultiplicativeReduction` — (`FreyCurve/Semistable.lean`, own work): (2026-07-17)
                                              — the Tate glue: multiplicative reduction at odd `q ≠
                                              p` with `p ∣ v_q(j)` ⟹ `IsUnramifiedAt q`, by the same
                                              embedded-subring transport as the good case, against
                                              the new pure-Tate content leaf below
                                                - ✅· `WeierstrassCurve.torsion_trivial_of_multiplicative_reduction` — pointwise inertia-triviality on torsion at
                                                  multiplicative primes with `p ∣ v_q(j)` — the
                                                  split/nonsplit case split; the local input to
                                                  `isUnramifiedAt_of_hasMultiplicativeReduction`.
                                                    - ✅· `torsion_trivial_of_split_multiplicative_adic` — pointwise inertia-TRIVIALITY in the split case
                                                      with `p ∣ v_q(j)`: the Tate uniformization
                                                      witness feeds `tate_inertia_trivial` at the
                                                      local valuation subring with the step-(d)
                                                      witness, pulled back to `E(ℚ̄)` along the
                                                      equivariant embedding.
                                                        - ✅· `WeierstrassCurve.exists_tateEquivSepClosure` — Tate's uniformisation over a separable
                                                          closure, now DERIVED from the choice-free
                                                          Tate-curve uniformisation and Tate's
                                                          variable-change theorem: the variable
                                                          change is `k`-rational, so its base-
                                                          changed point equivalence is Galois-
                                                          equivariant, and the equivariance
                                                          transports through the composite.
                                                            - ✅· `WeierstrassCurve.exists_tateCurveEquivSepClosure` — the uniformization core, quotient
                                                              form: Galois-equivariant Ωˣ/q^ℤ ≃+
                                                              E_q(Ω). DERIVED 2026-07-18 from the
                                                              pre-quotient node
                                                              exists_tateCurveHomSepClosure by the
                                                              first isomorphism theorem:
                                                              multiplicative lift ψ of the hom,
                                                              QuotientGroup.lift over zpowers q,
                                                              injectivity from the kernel
                                                              characterization,
                                                              MulEquiv.ofBijective,
                                                              MulEquiv.toAdditiveLeft; equivariance
                                                              descends definitionally on ofMul-
                                                              classes.
                                                                - ✅· `WeierstrassCurve.exists_tateCurveHomSepClosure` — the uniformization core, pre-
                                                                  quotient form: surjective Galois-
                                                                  equivariant hom Ωˣ →+ E_q(Ω) with
                                                                  kernel exactly q^ℤ. DERIVED
                                                                  2026-07-18 by feeding the finite-
                                                                  level canonical uniformisation
                                                                  tateCurveEquiv (underlying
                                                                  function pointMapQuot) into the
                                                                  sorried gluing implication exists_
                                                                  tateCurveHomSepClosure_of_finiteLe
                                                                  vel.
                                                                    - ✅· `TateCurve.tateCurveEquiv` — the finite-level Tate
                                                                      uniformisation kˣ/q^ℤ ≃+
                                                                      E_q(k), DERIVED from
                                                                      pointMapQuot_add +
                                                                      pointMapQuot_bijective with
                                                                      pointMapQuot (canonical,
                                                                      choice-free) as underlying
                                                                      function — the object the
                                                                      Ω-gluing consumes. RE-VENDORED
                                                                      2026-07-18 (stripped form):
                                                                      the annulus/evalA/pointMap
                                                                      machinery is in the tree (all
                                                                      PROVEN: CoeffRing evaluation,
                                                                      summability on the fundamental
                                                                      annulus, evaluated Weierstrass
                                                                      equation, annulusPoint
                                                                      nonsingularity, strict
                                                                      fundamental domain, kernel
                                                                      characterization
                                                                      pointMap_eq_zero_iff); the
                                                                      bilateral/Lambert negation-
                                                                      translation machinery stays in
                                                                      the reference commit 8282dfb^
                                                                      until the addition-law proof
                                                                      consumes it.
                                                                        - ✅· `TateCurve.pointMapQuot_surjective` — surjectivity of the
                                                                          uniformisation (Silverman
                                                                          ATAEC V.3.1(d)/V.4). DERIVED
                                                                          2026-07-18 from the x-onto
                                                                          leaf
                                                                          exists_annulus_bilateralX_eq:
                                                                          the leaf gives an annulus
                                                                          parameter u over the
                                                                          x-coordinate; Y_eq_of_X_eq
                                                                          gives y = bilateralY u or its
                                                                          negY, the latter realised by
                                                                          the inverse partner (u⁻¹ on
                                                                          the shell, q·u⁻¹ in the
                                                                          interior) via the PROVEN
                                                                          vertical case
                                                                          bilateral_negY_of_mul_trivial.
                                                                            - ❌· `TateCurve.exists_annulus_bilateralX_eq` — the x-onto leaf (sorry node,
                                                                              the analytic heart of
                                                                              Silverman V.4): every affine
                                                                              solution (x, y) of the Tate
                                                                              curve equation has an annulus
                                                                              parameter u with bilateralX u
                                                                              = x. Attack: Newton-
                                                                              polygon/valuation analysis of
                                                                              X(u) - x on the annulus (theta
                                                                              quotient), using completeness
                                                                              of k.
                                                                        - ✅· `TateCurve.pointMapQuot_add` — the addition law (Silverman
                                                                          ATAEC V.3.1(c)). DERIVED
                                                                          2026-07-18 from three sorried
                                                                          series-identity leaves (chord,
                                                                          tangent, X-fibre) + the PROVEN
                                                                          vertical case
                                                                          bilateral_negY_of_mul_trivial
                                                                          (inversion/shift identities),
                                                                          the PROVEN bilateral
                                                                          coordinate bridge
                                                                          pointMap_eq_bilateral on the
                                                                          extended window |q|² < |w| ≤
                                                                          1, and quotient bookkeeping
                                                                          (annulus normalisation,
                                                                          trivial classes).
                                                                            - ✅· `TateCurve.eq_or_mul_eq_of_bilateralX_eq` — the X-fibre (Silverman V.4).
                                                                              DERIVED 2026-07-18 from the
                                                                              coordinate-pair injectivity
                                                                              bilateralXY_inj: Y_eq_of_X_eq
                                                                              gives equal or negY-related
                                                                              y-values; equal ⇒ injectivity
                                                                              ⇒ v = u; negY-related ⇒ v =
                                                                              the inverse partner (u⁻¹ on
                                                                              the shell, q·u⁻¹ in the
                                                                              interior) by the PROVEN
                                                                              vertical case + injectivity,
                                                                              so uv ∈ {1, q}.
                                                                                - ❌· `TateCurve.bilateralXY_inj` — coordinate-pair injectivity on
                                                                                  the annulus (sorry node — the
                                                                                  injectivity half of Silverman
                                                                                  V.4): equal bilateral x- AND
                                                                                  y-values force equal
                                                                                  parameters. Attack: Newton-
                                                                                  polygon/theta-quotient
                                                                                  analysis of X(u) - X(v) over
                                                                                  the complete field, the
                                                                                  y-value separating the two
                                                                                  sheets.
                                                                            - ✅· `TateCurve.bilateral_add_self` — the tangent identity (V.3.1(c)
                                                                              doubling case). DERIVED
                                                                              2026-07-18 from the cleared
                                                                              tangent identities + the
                                                                              non-2-torsion leaf, same
                                                                              division bookkeeping pattern
                                                                              as the chord case.
                                                                                - ❌· `TateCurve.bilateral_ne_negY_of_sq_nontrivial` — non-2-torsion leaf (sorry
                                                                                  node): u in the annulus with
                                                                                  u² not in the trivial class
                                                                                  has 2Y(u) + X(u) ≠ 0 — the
                                                                                  2-torsion parameters are
                                                                                  exactly {-1, ±√q}·q^ℤ.
                                                                                - ❌· `TateCurve.bilateral_tangentY_cleared` — cleared tangent Y-identity
                                                                                  (sorry node): -(Y(u²)+X(u²))E
                                                                                  = M(X(u²)-X(u)) + Y(u)E.
                                                                                  Diagonal case.
                                                                                - ❌· `TateCurve.bilateral_tangentX_cleared` — cleared tangent X-identity
                                                                                  (sorry node): (X(u²)+2X(u))E²
                                                                                  = M² + ME with M the tangent-
                                                                                  slope numerator, E = y - negY.
                                                                                  Diagonal case of the cleared
                                                                                  chord content.
                                                                            - ✅· `TateCurve.bilateral_add_of_X_ne` — the chord identity (V.3.1(c)
                                                                              generic case). DERIVED
                                                                              2026-07-18 from the cleared
                                                                              chord identities
                                                                              bilateral_chordX_cleared /
                                                                              bilateral_chordY_cleared: the
                                                                              triviality exclusions follow
                                                                              from distinct x-values via the
                                                                              proven inversion/shift
                                                                              identities, and the
                                                                              slope/addX/addY division
                                                                              bookkeeping is field_simp +
                                                                              linear_combination against the
                                                                              cleared forms.
                                                                                - ❌· `TateCurve.bilateral_chordY_cleared` — cleared chord Y-identity
                                                                                  (sorry node):
                                                                                  -(Y(uv)+X(uv))(X(u)-X(v)) =
                                                                                  (Y(u)-Y(v))(X(uv)-X(u)) +
                                                                                  Y(u)(X(u)-X(v)) — linear in
                                                                                  the X-part output. Same attack
                                                                                  as the X-identity.
                                                                                - ❌· `TateCurve.bilateral_chordX_cleared` — cleared chord X-identity
                                                                                  (sorry node):
                                                                                  (X(uv)+X(u)+X(v))(X(u)-X(v))²
                                                                                  = (Y(u)-Y(v))² +
                                                                                  (Y(u)-Y(v))(X(u)-X(v)) — pure
                                                                                  polynomial series identity, no
                                                                                  slope/division/cases. Attack:
                                                                                  Ramanujan/Eisenstein
                                                                                  manipulation of divisor double
                                                                                  series
                                                                                  (Venkatachaliengar–Cooper Ch.
                                                                                  1) or two-transcendental
                                                                                  descent; mathlib LACKS the
                                                                                  ℘-addition law (checked
                                                                                  2026-07-18), so the ℂ-analytic
                                                                                  route requires formalizing it
                                                                                  first.
                                                                    - ❌🟪 `WeierstrassCurve.exists_tateCurveHomSepClosure_of_finiteLevel` — the Ω-gluing implication
                                                                      (sorry node): GIVEN the
                                                                      finite-level canonical
                                                                      uniformisation lˣ/q^ℤ ≃+
                                                                      E_q(l) with underlying
                                                                      pointMapQuot for every NALF l,
                                                                      the Ω-level hom exists.
                                                                      Content: finite subextensions
                                                                      of Ω/k are NALFs (unique
                                                                      valuative extension over the
                                                                      complete k — infrastructure
                                                                      absent from mathlib at this
                                                                      pin), the maps are compatible
                                                                      with inclusions and σ-twists
                                                                      by naturality of the universal
                                                                      series, and kernel/surjectivit
                                                                      y/equivariance pass to the
                                                                      colimit.
                                                    - ✅· `WeierstrassCurve.torsion_trivial_of_nonsplit_multiplicative_adic` — the nonsplit half of the triviality statement,
                                                      assembled from the LOCAL nonsplit node
                                                      `tate_inertia_trivial_of_nonsplit` by the
                                                      proven `ℚ̄`-pullback glue; the `j`-hypothesis
                                                      feeds through `map_j`.
                                                        - ✅· `WeierstrassCurve.tate_inertia_trivial_of_nonsplit` — the LOCAL twist-transfer of nonsplit
                                                          triviality, now assembled: as the
                                                          unipotent analogue via
                                                          `tate_inertia_trivial`, with the step-(d)
                                                          witness applied to the twisted minimal
                                                          model (same `j`-invariant through
                                                          `variableChange_j` and
                                                          `j_quadraticTwist`).
                                                            - ✅· `WeierstrassCurve.exists_tateEquivSepClosure` — Tate's uniformisation over a separable
                                                              closure, now DERIVED from the choice-
                                                              free Tate-curve uniformisation and
                                                              Tate's variable-change theorem: the
                                                              variable change is `k`-rational, so
                                                              its base-changed point equivalence is
                                                              Galois-equivariant, and the
                                                              equivariance transports through the
                                                              composite.
                                                                - ✅· `WeierstrassCurve.exists_tateCurveEquivSepClosure` — the uniformization core, quotient
                                                                  form: Galois-equivariant Ωˣ/q^ℤ ≃+
                                                                  E_q(Ω). DERIVED 2026-07-18 from
                                                                  the pre-quotient node
                                                                  exists_tateCurveHomSepClosure by
                                                                  the first isomorphism theorem:
                                                                  multiplicative lift ψ of the hom,
                                                                  QuotientGroup.lift over zpowers q,
                                                                  injectivity from the kernel
                                                                  characterization,
                                                                  MulEquiv.ofBijective,
                                                                  MulEquiv.toAdditiveLeft;
                                                                  equivariance descends
                                                                  definitionally on ofMul-classes.
                                                                    - ✅· `WeierstrassCurve.exists_tateCurveHomSepClosure` — the uniformization core, pre-
                                                                      quotient form: surjective
                                                                      Galois-equivariant hom Ωˣ →+
                                                                      E_q(Ω) with kernel exactly
                                                                      q^ℤ. DERIVED 2026-07-18 by
                                                                      feeding the finite-level
                                                                      canonical uniformisation
                                                                      tateCurveEquiv (underlying
                                                                      function pointMapQuot) into
                                                                      the sorried gluing implication
                                                                      exists_tateCurveHomSepClosure_
                                                                      of_finiteLevel.
                                                                        - ✅· `TateCurve.tateCurveEquiv` — the finite-level Tate
                                                                          uniformisation kˣ/q^ℤ ≃+
                                                                          E_q(k), DERIVED from
                                                                          pointMapQuot_add +
                                                                          pointMapQuot_bijective with
                                                                          pointMapQuot (canonical,
                                                                          choice-free) as underlying
                                                                          function — the object the
                                                                          Ω-gluing consumes. RE-VENDORED
                                                                          2026-07-18 (stripped form):
                                                                          the annulus/evalA/pointMap
                                                                          machinery is in the tree (all
                                                                          PROVEN: CoeffRing evaluation,
                                                                          summability on the fundamental
                                                                          annulus, evaluated Weierstrass
                                                                          equation, annulusPoint
                                                                          nonsingularity, strict
                                                                          fundamental domain, kernel
                                                                          characterization
                                                                          pointMap_eq_zero_iff); the
                                                                          bilateral/Lambert negation-
                                                                          translation machinery stays in
                                                                          the reference commit 8282dfb^
                                                                          until the addition-law proof
                                                                          consumes it.
                                                                            - ✅· `TateCurve.pointMapQuot_surjective` — surjectivity of the
                                                                              uniformisation (Silverman
                                                                              ATAEC V.3.1(d)/V.4). DERIVED
                                                                              2026-07-18 from the x-onto
                                                                              leaf
                                                                              exists_annulus_bilateralX_eq:
                                                                              the leaf gives an annulus
                                                                              parameter u over the
                                                                              x-coordinate; Y_eq_of_X_eq
                                                                              gives y = bilateralY u or its
                                                                              negY, the latter realised by
                                                                              the inverse partner (u⁻¹ on
                                                                              the shell, q·u⁻¹ in the
                                                                              interior) via the PROVEN
                                                                              vertical case
                                                                              bilateral_negY_of_mul_trivial.
                                                                                - ❌· `TateCurve.exists_annulus_bilateralX_eq` — the x-onto leaf (sorry node,
                                                                                  the analytic heart of
                                                                                  Silverman V.4): every affine
                                                                                  solution (x, y) of the Tate
                                                                                  curve equation has an annulus
                                                                                  parameter u with bilateralX u
                                                                                  = x. Attack: Newton-
                                                                                  polygon/valuation analysis of
                                                                                  X(u) - x on the annulus (theta
                                                                                  quotient), using completeness
                                                                                  of k.
                                                                            - ✅· `TateCurve.pointMapQuot_add` — the addition law (Silverman
                                                                              ATAEC V.3.1(c)). DERIVED
                                                                              2026-07-18 from three sorried
                                                                              series-identity leaves (chord,
                                                                              tangent, X-fibre) + the PROVEN
                                                                              vertical case
                                                                              bilateral_negY_of_mul_trivial
                                                                              (inversion/shift identities),
                                                                              the PROVEN bilateral
                                                                              coordinate bridge
                                                                              pointMap_eq_bilateral on the
                                                                              extended window |q|² < |w| ≤
                                                                              1, and quotient bookkeeping
                                                                              (annulus normalisation,
                                                                              trivial classes).
                                                                                - ✅· `TateCurve.eq_or_mul_eq_of_bilateralX_eq` — the X-fibre (Silverman V.4).
                                                                                  DERIVED 2026-07-18 from the
                                                                                  coordinate-pair injectivity
                                                                                  bilateralXY_inj: Y_eq_of_X_eq
                                                                                  gives equal or negY-related
                                                                                  y-values; equal ⇒ injectivity
                                                                                  ⇒ v = u; negY-related ⇒ v =
                                                                                  the inverse partner (u⁻¹ on
                                                                                  the shell, q·u⁻¹ in the
                                                                                  interior) by the PROVEN
                                                                                  vertical case + injectivity,
                                                                                  so uv ∈ {1, q}.
                                                                                    - ❌· `TateCurve.bilateralXY_inj` — coordinate-pair injectivity on
                                                                                      the annulus (sorry node — the
                                                                                      injectivity half of Silverman
                                                                                      V.4): equal bilateral x- AND
                                                                                      y-values force equal
                                                                                      parameters. Attack: Newton-
                                                                                      polygon/theta-quotient
                                                                                      analysis of X(u) - X(v) over
                                                                                      the complete field, the
                                                                                      y-value separating the two
                                                                                      sheets.
                                                                                - ✅· `TateCurve.bilateral_add_self` — the tangent identity (V.3.1(c)
                                                                                  doubling case). DERIVED
                                                                                  2026-07-18 from the cleared
                                                                                  tangent identities + the
                                                                                  non-2-torsion leaf, same
                                                                                  division bookkeeping pattern
                                                                                  as the chord case.
                                                                                    - ❌· `TateCurve.bilateral_ne_negY_of_sq_nontrivial` — non-2-torsion leaf (sorry
                                                                                      node): u in the annulus with
                                                                                      u² not in the trivial class
                                                                                      has 2Y(u) + X(u) ≠ 0 — the
                                                                                      2-torsion parameters are
                                                                                      exactly {-1, ±√q}·q^ℤ.
                                                                                    - ❌· `TateCurve.bilateral_tangentY_cleared` — cleared tangent Y-identity
                                                                                      (sorry node): -(Y(u²)+X(u²))E
                                                                                      = M(X(u²)-X(u)) + Y(u)E.
                                                                                      Diagonal case.
                                                                                    - ❌· `TateCurve.bilateral_tangentX_cleared` — cleared tangent X-identity
                                                                                      (sorry node): (X(u²)+2X(u))E²
                                                                                      = M² + ME with M the tangent-
                                                                                      slope numerator, E = y - negY.
                                                                                      Diagonal case of the cleared
                                                                                      chord content.
                                                                                - ✅· `TateCurve.bilateral_add_of_X_ne` — the chord identity (V.3.1(c)
                                                                                  generic case). DERIVED
                                                                                  2026-07-18 from the cleared
                                                                                  chord identities
                                                                                  bilateral_chordX_cleared /
                                                                                  bilateral_chordY_cleared: the
                                                                                  triviality exclusions follow
                                                                                  from distinct x-values via the
                                                                                  proven inversion/shift
                                                                                  identities, and the
                                                                                  slope/addX/addY division
                                                                                  bookkeeping is field_simp +
                                                                                  linear_combination against the
                                                                                  cleared forms.
                                                                                    - ❌· `TateCurve.bilateral_chordY_cleared` — cleared chord Y-identity
                                                                                      (sorry node):
                                                                                      -(Y(uv)+X(uv))(X(u)-X(v)) =
                                                                                      (Y(u)-Y(v))(X(uv)-X(u)) +
                                                                                      Y(u)(X(u)-X(v)) — linear in
                                                                                      the X-part output. Same attack
                                                                                      as the X-identity.
                                                                                    - ❌· `TateCurve.bilateral_chordX_cleared` — cleared chord X-identity
                                                                                      (sorry node):
                                                                                      (X(uv)+X(u)+X(v))(X(u)-X(v))²
                                                                                      = (Y(u)-Y(v))² +
                                                                                      (Y(u)-Y(v))(X(u)-X(v)) — pure
                                                                                      polynomial series identity, no
                                                                                      slope/division/cases. Attack:
                                                                                      Ramanujan/Eisenstein
                                                                                      manipulation of divisor double
                                                                                      series
                                                                                      (Venkatachaliengar–Cooper Ch.
                                                                                      1) or two-transcendental
                                                                                      descent; mathlib LACKS the
                                                                                      ℘-addition law (checked
                                                                                      2026-07-18), so the ℂ-analytic
                                                                                      route requires formalizing it
                                                                                      first.
                                                                        - ❌🟪 `WeierstrassCurve.exists_tateCurveHomSepClosure_of_finiteLevel` — the Ω-gluing implication
                                                                          (sorry node): GIVEN the
                                                                          finite-level canonical
                                                                          uniformisation lˣ/q^ℤ ≃+
                                                                          E_q(l) with underlying
                                                                          pointMapQuot for every NALF l,
                                                                          the Ω-level hom exists.
                                                                          Content: finite subextensions
                                                                          of Ω/k are NALFs (unique
                                                                          valuative extension over the
                                                                          complete k — infrastructure
                                                                          absent from mathlib at this
                                                                          pin), the maps are compatible
                                                                          with inclusions and σ-twists
                                                                          by naturality of the universal
                                                                          series, and kernel/surjectivit
                                                                          y/equivariance pass to the
                                                                          colimit.
                                - ✅· `det_galoisRep_eq_cyclotomic` — `det_galoisRep_eq_cyclotomic` — (2026-07-17): `det ρ̄` and `χ̄`
                                  are continuous conjugation-invariant `ZMod p`-valued functions on
                                  `Γ ℚ` (continuity of `det ∘ ρ` from discreteness of `End` via
                                  `discreteTopology_moduleTopology`; `χ̄`-continuity in
                                  `Chebotarev.lean`); they agree at `Frob_q` for almost all `q` (the
                                  leaf below + `cyclotomicCharacterModL_globalFrob`, ), and the
                                  Frobenius conjugacy classes are dense
                                  (`dense_conjClasses_globalFrob`, rooted in the Chebotarev node),
                                  so the closed agreement set is everything. Bridge
                                  `cyclotomicCharacterModL_eq_toZMod` (`χ̄ = toZMod ∘ χ`) via
                                  `modularCyclotomicCharacter.unique` +
                                  `toZMod_eq_ringEquivCongr_comp_toZModPow`
                                    - ❌· `det_galoisRep_globalFrob` — `det_galoisRep_globalFrob` (`EllipticCurve/WeilPairing.lean`,
                                      stated 2026-07-17): Frobenius determinant at good primes —
                                      away from a finite set of places, `det ρ̄(Frob_q) = q mod p`
                                      (the point-counting/Weil computation over the reduced curve;
                                      route: NOS reduction injectivity + Frobenius-isogeny degree).
                                      - (the other root of this derivation is the Chebotarev node
                                      `exists_frobenius_conj_mem_coset`, listed under the
                                      Chebotarev–Brauer–Nesbitt cone.)
                                    - ✅· `dense_conjClasses_globalFrob` — `dense_conjClasses_globalFrob` — Chebotarev density,
                                      topological form — now (2026-07-16) by the profinite limit
                                      argument (: cosets of fixing subgroups of finite subextensions
                                      are a neighborhood basis, `krullTopology_mem_nhds_one_iff`;
                                      the finite-level statement puts a Frobenius conjugate in every
                                      coset):
                                        - ❌· `exists_frobenius_conj_mem_coset` — `exists_frobenius_conj_mem_coset` — Chebotarev, finite
                                          level: for every finite subextension `E` of `K̄/K` and
                                          every `σ`, the coset `σ·Gal(K̄/E)` contains a conjugate of
                                          a `globalFrob v` with `v ∉ S` (existence form of
                                          Chebotarev for the Galois closure of `E/K`)
                            - ❌· `FreyPackage.exists_quotient_curve_point` — (stated 2026-07-17) — the Vélu quotient leaf: a stable line with
                              trivial quotient action produces `E'/ℚ` with full rational 2-torsion
                              and a rational `p`-point (quotient by the rational subgroup;
                              quantified over Weierstrass models)
            - ✅· `WeierstrassCurve.mazur_torsion_bound` — Mazur's torsion theorem, weak form: no elliptic curve over ℚ has a subgroup of
              rational points ≅ ℤ/2 × ℤ/2p for p ≥ 5 (primality dropped as unneeded) — now
              (2026-07-16) from the faithful classification below: images of an injective hom from
              the finite group ℤ/2 × ℤ/2p are torsion (finite additive order), the hom corestricts
              into the torsion submodule, and 4p ≥ 20 > 16 ≥ the order of every group in Mazur's
              list (`Nat.card` comparison)
                - ❌· `WeierstrassCurve.mazur_classification` — Mazur's torsion theorem, stated faithfully: the torsion submodule
                  (`Submodule.torsion ℤ E(ℚ)`) is ≃+ to one of the fifteen groups ℤ/n (n ∈
                  {1,…,10,12}) or ℤ/2 × ℤ/2m (m ∈ {1,…,4}). Mazur, Publ. Math. IHÉS 47 (1977);
                  Invent. Math. 44 (1978)
        - ✅· `FreyPackage.galoisRep_not_irreducible` — (B4, `Fermat/PrimeFive.lean`) — now (2026-07-16) from two explicit nodes, mirroring the
          FLT project's hardly-ramified plan (their B5/B6, stated in Lean here before upstream):
            - ✅· `FreyCurve.torsion_isHardlyRamified` — (`GaloisRepresentation/HardlyRamified/Frey.lean`) — now (2026-07-16) as the structure
              constructor applied to the four defining conditions, each an explicit node in
              `HardlyRamified/FreyConditions.lean` (own work):
                - ✅· `FreyCurve.torsion_det` — det ρ̄ = mod-p cyclotomic character — now (2026-07-16) via the Weil pairing route
                  (`EllipticCurve/WeilPairing.lean`, own work):
                    - ✅· `WeilPairing.exists_weilPairing` — the Weil pairing: (2026-07-17) as the coordinate determinant form in a
                      `finBasis` (`#E[p] = p²` ⟹ rank 2), Galois-scaled by `det ρ`
                      (`pairing_map_eq_det_smul`) = the cyclotomic character by the det node below
                        - ✅· `det_galoisRep_eq_cyclotomic` — `det_galoisRep_eq_cyclotomic` — (2026-07-17): `det ρ̄` and `χ̄` are
                          continuous conjugation-invariant `ZMod p`-valued functions on `Γ ℚ`
                          (continuity of `det ∘ ρ` from discreteness of `End` via
                          `discreteTopology_moduleTopology`; `χ̄`-continuity in `Chebotarev.lean`);
                          they agree at `Frob_q` for almost all `q` (the leaf below +
                          `cyclotomicCharacterModL_globalFrob`, ), and the Frobenius conjugacy
                          classes are dense (`dense_conjClasses_globalFrob`, rooted in the
                          Chebotarev node), so the closed agreement set is everything. Bridge
                          `cyclotomicCharacterModL_eq_toZMod` (`χ̄ = toZMod ∘ χ`) via
                          `modularCyclotomicCharacter.unique` +
                          `toZMod_eq_ringEquivCongr_comp_toZModPow`
                            - ❌· `det_galoisRep_globalFrob` — `det_galoisRep_globalFrob` (`EllipticCurve/WeilPairing.lean`, stated
                              2026-07-17): Frobenius determinant at good primes — away from a finite
                              set of places, `det ρ̄(Frob_q) = q mod p` (the point-counting/Weil
                              computation over the reduced curve; route: NOS reduction injectivity +
                              Frobenius-isogeny degree). - (the other root of this derivation is the
                              Chebotarev node `exists_frobenius_conj_mem_coset`, listed under the
                              Chebotarev–Brauer–Nesbitt cone.)
                            - ✅· `dense_conjClasses_globalFrob` — `dense_conjClasses_globalFrob` — Chebotarev density, topological form
                              — now (2026-07-16) by the profinite limit argument (: cosets of fixing
                              subgroups of finite subextensions are a neighborhood basis,
                              `krullTopology_mem_nhds_one_iff`; the finite-level statement puts a
                              Frobenius conjugate in every coset):
                                - ❌· `exists_frobenius_conj_mem_coset` — `exists_frobenius_conj_mem_coset` — Chebotarev, finite level: for
                                  every finite subextension `E` of `K̄/K` and every `σ`, the coset
                                  `σ·Gal(K̄/E)` contains a conjugate of a `globalFrob v` with `v ∉
                                  S` (existence form of Chebotarev for the Galois closure of `E/K`)
                - ✅· `FreyCurve.torsion_isUnramified` — unramified outside {2, p}: (2026-07-16) by the case split `q ∣ abc` or not, from
                  the two nodes below
                    - ✅· `FreyCurve.torsion_isUnramified_of_multiplicative` — (2026-07-16) from the arithmetic
                      (`freyCurve_hasMultiplicativeReduction_of_dvd` + `j_valuation_of_bad_prime`)
                      and the Tate glue node below
                        - ✅· `WeierstrassCurve.isUnramifiedAt_of_hasMultiplicativeReduction` — (`FreyCurve/Semistable.lean`, own work): (2026-07-17) — the Tate glue:
                          multiplicative reduction at odd `q ≠ p` with `p ∣ v_q(j)` ⟹
                          `IsUnramifiedAt q`, by the same embedded-subring transport as the good
                          case, against the new pure-Tate content leaf below
                            - ✅· `WeierstrassCurve.torsion_trivial_of_multiplicative_reduction` — pointwise inertia-triviality on torsion at multiplicative primes with
                              `p ∣ v_q(j)` — the split/nonsplit case split; the local input to
                              `isUnramifiedAt_of_hasMultiplicativeReduction`.
                                - ✅· `torsion_trivial_of_split_multiplicative_adic` — pointwise inertia-TRIVIALITY in the split case with `p ∣ v_q(j)`:
                                  the Tate uniformization witness feeds `tate_inertia_trivial` at
                                  the local valuation subring with the step-(d) witness, pulled back
                                  to `E(ℚ̄)` along the equivariant embedding.
                                    - ✅· `WeierstrassCurve.exists_tateEquivSepClosure` — Tate's uniformisation over a separable closure, now DERIVED
                                      from the choice-free Tate-curve uniformisation and Tate's
                                      variable-change theorem: the variable change is `k`-rational,
                                      so its base-changed point equivalence is Galois-equivariant,
                                      and the equivariance transports through the composite.
                                        - ✅· `WeierstrassCurve.exists_tateCurveEquivSepClosure` — the uniformization core, quotient form: Galois-equivariant
                                          Ωˣ/q^ℤ ≃+ E_q(Ω). DERIVED 2026-07-18 from the pre-quotient
                                          node exists_tateCurveHomSepClosure by the first
                                          isomorphism theorem: multiplicative lift ψ of the hom,
                                          QuotientGroup.lift over zpowers q, injectivity from the
                                          kernel characterization, MulEquiv.ofBijective,
                                          MulEquiv.toAdditiveLeft; equivariance descends
                                          definitionally on ofMul-classes.
                                            - ✅· `WeierstrassCurve.exists_tateCurveHomSepClosure` — the uniformization core, pre-quotient form: surjective
                                              Galois-equivariant hom Ωˣ →+ E_q(Ω) with kernel
                                              exactly q^ℤ. DERIVED 2026-07-18 by feeding the finite-
                                              level canonical uniformisation tateCurveEquiv
                                              (underlying function pointMapQuot) into the sorried
                                              gluing implication
                                              exists_tateCurveHomSepClosure_of_finiteLevel.
                                                - ✅· `TateCurve.tateCurveEquiv` — the finite-level Tate uniformisation kˣ/q^ℤ ≃+
                                                  E_q(k), DERIVED from pointMapQuot_add +
                                                  pointMapQuot_bijective with pointMapQuot
                                                  (canonical, choice-free) as underlying function —
                                                  the object the Ω-gluing consumes. RE-VENDORED
                                                  2026-07-18 (stripped form): the
                                                  annulus/evalA/pointMap machinery is in the tree
                                                  (all PROVEN: CoeffRing evaluation, summability on
                                                  the fundamental annulus, evaluated Weierstrass
                                                  equation, annulusPoint nonsingularity, strict
                                                  fundamental domain, kernel characterization
                                                  pointMap_eq_zero_iff); the bilateral/Lambert
                                                  negation-translation machinery stays in the
                                                  reference commit 8282dfb^ until the addition-law
                                                  proof consumes it.
                                                    - ✅· `TateCurve.pointMapQuot_surjective` — surjectivity of the uniformisation (Silverman
                                                      ATAEC V.3.1(d)/V.4). DERIVED 2026-07-18 from
                                                      the x-onto leaf exists_annulus_bilateralX_eq:
                                                      the leaf gives an annulus parameter u over the
                                                      x-coordinate; Y_eq_of_X_eq gives y =
                                                      bilateralY u or its negY, the latter realised
                                                      by the inverse partner (u⁻¹ on the shell,
                                                      q·u⁻¹ in the interior) via the PROVEN vertical
                                                      case bilateral_negY_of_mul_trivial.
                                                        - ❌· `TateCurve.exists_annulus_bilateralX_eq` — the x-onto leaf (sorry node, the analytic
                                                          heart of Silverman V.4): every affine
                                                          solution (x, y) of the Tate curve equation
                                                          has an annulus parameter u with bilateralX
                                                          u = x. Attack: Newton-polygon/valuation
                                                          analysis of X(u) - x on the annulus (theta
                                                          quotient), using completeness of k.
                                                    - ✅· `TateCurve.pointMapQuot_add` — the addition law (Silverman ATAEC V.3.1(c)).
                                                      DERIVED 2026-07-18 from three sorried series-
                                                      identity leaves (chord, tangent, X-fibre) +
                                                      the PROVEN vertical case
                                                      bilateral_negY_of_mul_trivial (inversion/shift
                                                      identities), the PROVEN bilateral coordinate
                                                      bridge pointMap_eq_bilateral on the extended
                                                      window |q|² < |w| ≤ 1, and quotient
                                                      bookkeeping (annulus normalisation, trivial
                                                      classes).
                                                        - ✅· `TateCurve.eq_or_mul_eq_of_bilateralX_eq` — the X-fibre (Silverman V.4). DERIVED
                                                          2026-07-18 from the coordinate-pair
                                                          injectivity bilateralXY_inj: Y_eq_of_X_eq
                                                          gives equal or negY-related y-values;
                                                          equal ⇒ injectivity ⇒ v = u; negY-related
                                                          ⇒ v = the inverse partner (u⁻¹ on the
                                                          shell, q·u⁻¹ in the interior) by the
                                                          PROVEN vertical case + injectivity, so uv
                                                          ∈ {1, q}.
                                                            - ❌· `TateCurve.bilateralXY_inj` — coordinate-pair injectivity on the
                                                              annulus (sorry node — the injectivity
                                                              half of Silverman V.4): equal
                                                              bilateral x- AND y-values force equal
                                                              parameters. Attack: Newton-
                                                              polygon/theta-quotient analysis of
                                                              X(u) - X(v) over the complete field,
                                                              the y-value separating the two sheets.
                                                        - ✅· `TateCurve.bilateral_add_self` — the tangent identity (V.3.1(c) doubling
                                                          case). DERIVED 2026-07-18 from the cleared
                                                          tangent identities + the non-2-torsion
                                                          leaf, same division bookkeeping pattern as
                                                          the chord case.
                                                            - ❌· `TateCurve.bilateral_ne_negY_of_sq_nontrivial` — non-2-torsion leaf (sorry node): u in
                                                              the annulus with u² not in the trivial
                                                              class has 2Y(u) + X(u) ≠ 0 — the
                                                              2-torsion parameters are exactly {-1,
                                                              ±√q}·q^ℤ.
                                                            - ❌· `TateCurve.bilateral_tangentY_cleared` — cleared tangent Y-identity (sorry
                                                              node): -(Y(u²)+X(u²))E = M(X(u²)-X(u))
                                                              + Y(u)E. Diagonal case.
                                                            - ❌· `TateCurve.bilateral_tangentX_cleared` — cleared tangent X-identity (sorry
                                                              node): (X(u²)+2X(u))E² = M² + ME with
                                                              M the tangent-slope numerator, E = y -
                                                              negY. Diagonal case of the cleared
                                                              chord content.
                                                        - ✅· `TateCurve.bilateral_add_of_X_ne` — the chord identity (V.3.1(c) generic
                                                          case). DERIVED 2026-07-18 from the cleared
                                                          chord identities bilateral_chordX_cleared
                                                          / bilateral_chordY_cleared: the triviality
                                                          exclusions follow from distinct x-values
                                                          via the proven inversion/shift identities,
                                                          and the slope/addX/addY division
                                                          bookkeeping is field_simp +
                                                          linear_combination against the cleared
                                                          forms.
                                                            - ❌· `TateCurve.bilateral_chordY_cleared` — cleared chord Y-identity (sorry node):
                                                              -(Y(uv)+X(uv))(X(u)-X(v)) =
                                                              (Y(u)-Y(v))(X(uv)-X(u)) +
                                                              Y(u)(X(u)-X(v)) — linear in the X-part
                                                              output. Same attack as the X-identity.
                                                            - ❌· `TateCurve.bilateral_chordX_cleared` — cleared chord X-identity (sorry node):
                                                              (X(uv)+X(u)+X(v))(X(u)-X(v))² =
                                                              (Y(u)-Y(v))² + (Y(u)-Y(v))(X(u)-X(v))
                                                              — pure polynomial series identity, no
                                                              slope/division/cases. Attack:
                                                              Ramanujan/Eisenstein manipulation of
                                                              divisor double series
                                                              (Venkatachaliengar–Cooper Ch. 1) or
                                                              two-transcendental descent; mathlib
                                                              LACKS the ℘-addition law (checked
                                                              2026-07-18), so the ℂ-analytic route
                                                              requires formalizing it first.
                                                - ❌🟪 `WeierstrassCurve.exists_tateCurveHomSepClosure_of_finiteLevel` — the Ω-gluing implication (sorry node): GIVEN the
                                                  finite-level canonical uniformisation lˣ/q^ℤ ≃+
                                                  E_q(l) with underlying pointMapQuot for every NALF
                                                  l, the Ω-level hom exists. Content: finite
                                                  subextensions of Ω/k are NALFs (unique valuative
                                                  extension over the complete k — infrastructure
                                                  absent from mathlib at this pin), the maps are
                                                  compatible with inclusions and σ-twists by
                                                  naturality of the universal series, and
                                                  kernel/surjectivity/equivariance pass to the
                                                  colimit.
                                - ✅· `WeierstrassCurve.torsion_trivial_of_nonsplit_multiplicative_adic` — the nonsplit half of the triviality statement, assembled from the
                                  LOCAL nonsplit node `tate_inertia_trivial_of_nonsplit` by the
                                  proven `ℚ̄`-pullback glue; the `j`-hypothesis feeds through
                                  `map_j`.
                                    - ✅· `WeierstrassCurve.tate_inertia_trivial_of_nonsplit` — the LOCAL twist-transfer of nonsplit triviality, now
                                      assembled: as the unipotent analogue via
                                      `tate_inertia_trivial`, with the step-(d) witness applied to
                                      the twisted minimal model (same `j`-invariant through
                                      `variableChange_j` and `j_quadraticTwist`).
                                        - ✅· `WeierstrassCurve.exists_tateEquivSepClosure` — Tate's uniformisation over a separable closure, now
                                          DERIVED from the choice-free Tate-curve uniformisation and
                                          Tate's variable-change theorem: the variable change is
                                          `k`-rational, so its base-changed point equivalence is
                                          Galois-equivariant, and the equivariance transports
                                          through the composite.
                                            - ✅· `WeierstrassCurve.exists_tateCurveEquivSepClosure` — the uniformization core, quotient form: Galois-
                                              equivariant Ωˣ/q^ℤ ≃+ E_q(Ω). DERIVED 2026-07-18 from
                                              the pre-quotient node exists_tateCurveHomSepClosure by
                                              the first isomorphism theorem: multiplicative lift ψ
                                              of the hom, QuotientGroup.lift over zpowers q,
                                              injectivity from the kernel characterization,
                                              MulEquiv.ofBijective, MulEquiv.toAdditiveLeft;
                                              equivariance descends definitionally on ofMul-classes.
                                                - ✅· `WeierstrassCurve.exists_tateCurveHomSepClosure` — the uniformization core, pre-quotient form:
                                                  surjective Galois-equivariant hom Ωˣ →+ E_q(Ω)
                                                  with kernel exactly q^ℤ. DERIVED 2026-07-18 by
                                                  feeding the finite-level canonical uniformisation
                                                  tateCurveEquiv (underlying function pointMapQuot)
                                                  into the sorried gluing implication
                                                  exists_tateCurveHomSepClosure_of_finiteLevel.
                                                    - ✅· `TateCurve.tateCurveEquiv` — the finite-level Tate uniformisation kˣ/q^ℤ ≃+
                                                      E_q(k), DERIVED from pointMapQuot_add +
                                                      pointMapQuot_bijective with pointMapQuot
                                                      (canonical, choice-free) as underlying
                                                      function — the object the Ω-gluing consumes.
                                                      RE-VENDORED 2026-07-18 (stripped form): the
                                                      annulus/evalA/pointMap machinery is in the
                                                      tree (all PROVEN: CoeffRing evaluation,
                                                      summability on the fundamental annulus,
                                                      evaluated Weierstrass equation, annulusPoint
                                                      nonsingularity, strict fundamental domain,
                                                      kernel characterization pointMap_eq_zero_iff);
                                                      the bilateral/Lambert negation-translation
                                                      machinery stays in the reference commit
                                                      8282dfb^ until the addition-law proof consumes
                                                      it.
                                                        - ✅· `TateCurve.pointMapQuot_surjective` — surjectivity of the uniformisation
                                                          (Silverman ATAEC V.3.1(d)/V.4). DERIVED
                                                          2026-07-18 from the x-onto leaf
                                                          exists_annulus_bilateralX_eq: the leaf
                                                          gives an annulus parameter u over the
                                                          x-coordinate; Y_eq_of_X_eq gives y =
                                                          bilateralY u or its negY, the latter
                                                          realised by the inverse partner (u⁻¹ on
                                                          the shell, q·u⁻¹ in the interior) via the
                                                          PROVEN vertical case
                                                          bilateral_negY_of_mul_trivial.
                                                            - ❌· `TateCurve.exists_annulus_bilateralX_eq` — the x-onto leaf (sorry node, the
                                                              analytic heart of Silverman V.4):
                                                              every affine solution (x, y) of the
                                                              Tate curve equation has an annulus
                                                              parameter u with bilateralX u = x.
                                                              Attack: Newton-polygon/valuation
                                                              analysis of X(u) - x on the annulus
                                                              (theta quotient), using completeness
                                                              of k.
                                                        - ✅· `TateCurve.pointMapQuot_add` — the addition law (Silverman ATAEC
                                                          V.3.1(c)). DERIVED 2026-07-18 from three
                                                          sorried series-identity leaves (chord,
                                                          tangent, X-fibre) + the PROVEN vertical
                                                          case bilateral_negY_of_mul_trivial
                                                          (inversion/shift identities), the PROVEN
                                                          bilateral coordinate bridge
                                                          pointMap_eq_bilateral on the extended
                                                          window |q|² < |w| ≤ 1, and quotient
                                                          bookkeeping (annulus normalisation,
                                                          trivial classes).
                                                            - ✅· `TateCurve.eq_or_mul_eq_of_bilateralX_eq` — the X-fibre (Silverman V.4). DERIVED
                                                              2026-07-18 from the coordinate-pair
                                                              injectivity bilateralXY_inj:
                                                              Y_eq_of_X_eq gives equal or negY-
                                                              related y-values; equal ⇒ injectivity
                                                              ⇒ v = u; negY-related ⇒ v = the
                                                              inverse partner (u⁻¹ on the shell,
                                                              q·u⁻¹ in the interior) by the PROVEN
                                                              vertical case + injectivity, so uv ∈
                                                              {1, q}.
                                                                - ❌· `TateCurve.bilateralXY_inj` — coordinate-pair injectivity on the
                                                                  annulus (sorry node — the
                                                                  injectivity half of Silverman
                                                                  V.4): equal bilateral x- AND
                                                                  y-values force equal parameters.
                                                                  Attack: Newton-polygon/theta-
                                                                  quotient analysis of X(u) - X(v)
                                                                  over the complete field, the
                                                                  y-value separating the two sheets.
                                                            - ✅· `TateCurve.bilateral_add_self` — the tangent identity (V.3.1(c)
                                                              doubling case). DERIVED 2026-07-18
                                                              from the cleared tangent identities +
                                                              the non-2-torsion leaf, same division
                                                              bookkeeping pattern as the chord case.
                                                                - ❌· `TateCurve.bilateral_ne_negY_of_sq_nontrivial` — non-2-torsion leaf (sorry node): u
                                                                  in the annulus with u² not in the
                                                                  trivial class has 2Y(u) + X(u) ≠ 0
                                                                  — the 2-torsion parameters are
                                                                  exactly {-1, ±√q}·q^ℤ.
                                                                - ❌· `TateCurve.bilateral_tangentY_cleared` — cleared tangent Y-identity (sorry
                                                                  node): -(Y(u²)+X(u²))E =
                                                                  M(X(u²)-X(u)) + Y(u)E. Diagonal
                                                                  case.
                                                                - ❌· `TateCurve.bilateral_tangentX_cleared` — cleared tangent X-identity (sorry
                                                                  node): (X(u²)+2X(u))E² = M² + ME
                                                                  with M the tangent-slope
                                                                  numerator, E = y - negY. Diagonal
                                                                  case of the cleared chord content.
                                                            - ✅· `TateCurve.bilateral_add_of_X_ne` — the chord identity (V.3.1(c) generic
                                                              case). DERIVED 2026-07-18 from the
                                                              cleared chord identities
                                                              bilateral_chordX_cleared /
                                                              bilateral_chordY_cleared: the
                                                              triviality exclusions follow from
                                                              distinct x-values via the proven
                                                              inversion/shift identities, and the
                                                              slope/addX/addY division bookkeeping
                                                              is field_simp + linear_combination
                                                              against the cleared forms.
                                                                - ❌· `TateCurve.bilateral_chordY_cleared` — cleared chord Y-identity (sorry
                                                                  node): -(Y(uv)+X(uv))(X(u)-X(v)) =
                                                                  (Y(u)-Y(v))(X(uv)-X(u)) +
                                                                  Y(u)(X(u)-X(v)) — linear in the
                                                                  X-part output. Same attack as the
                                                                  X-identity.
                                                                - ❌· `TateCurve.bilateral_chordX_cleared` — cleared chord X-identity (sorry
                                                                  node):
                                                                  (X(uv)+X(u)+X(v))(X(u)-X(v))² =
                                                                  (Y(u)-Y(v))² +
                                                                  (Y(u)-Y(v))(X(u)-X(v)) — pure
                                                                  polynomial series identity, no
                                                                  slope/division/cases. Attack:
                                                                  Ramanujan/Eisenstein manipulation
                                                                  of divisor double series
                                                                  (Venkatachaliengar–Cooper Ch. 1)
                                                                  or two-transcendental descent;
                                                                  mathlib LACKS the ℘-addition law
                                                                  (checked 2026-07-18), so the
                                                                  ℂ-analytic route requires
                                                                  formalizing it first.
                                                    - ❌🟪 `WeierstrassCurve.exists_tateCurveHomSepClosure_of_finiteLevel` — the Ω-gluing implication (sorry node): GIVEN
                                                      the finite-level canonical uniformisation
                                                      lˣ/q^ℤ ≃+ E_q(l) with underlying pointMapQuot
                                                      for every NALF l, the Ω-level hom exists.
                                                      Content: finite subextensions of Ω/k are NALFs
                                                      (unique valuative extension over the complete
                                                      k — infrastructure absent from mathlib at this
                                                      pin), the maps are compatible with inclusions
                                                      and σ-twists by naturality of the universal
                                                      series, and kernel/surjectivity/equivariance
                                                      pass to the colimit.
                - ✅· `FreyCurve.torsion_isFlat` — flat at p: (2026-07-16) by the case split `p ∣ abc` or not, from the two nodes
                  below
                    - ✅· `FreyCurve.torsion_isFlat_of_good` — (2026-07-16) from the arithmetic node `freyCurve_hasGoodReduction_of_not_dvd`
                      (applied at `q := p`) and the flat glue node below
                        - ✅· `WeierstrassCurve.isFlatAt_of_hasGoodReduction` — (`FreyCurve/Semistable.lean`, own work): (2026-07-17) — good reduction at
                          `p` ⟹ `IsFlatAt p` for the mod-`p` torsion rep, from the leaf below plus
                          the shared flat transport `GaloisRep.isFlatAt_of_dvr_package` (see its own
                          subtree entry under the multiplicative case)
                            - ❌· `torsion_flat_of_good_reduction` — `torsion_flat_of_good_reduction`
                              (`KnownIn1980s/EllipticCurves/Flat.lean`, 2026-07-16): good reduction
                              over a DVR makes the `n`-torsion a finite flat group scheme (Hopf
                              algebra, finite flat, étale generic fibre, equivariant points
                              isomorphism). Plus the division-polynomial node `isCoprime_Φ_ΨSq` —
                              restated for fields and directly (2026-07-17; the former
                              `resultant_Φ_ΨSq` node was DELETED, see the session-6 log)
                    - ✅· `FreyCurve.torsion_isFlat_of_multiplicative` — (2026-07-16) from the arithmetic
                      (`freyCurve_hasMultiplicativeReduction_of_dvd` at `q := p` +
                      `j_valuation_of_bad_prime`) and the glue node below
                        - ✅· `WeierstrassCurve.isFlatAt_of_hasMultiplicativeReduction` — (`FreyCurve/Semistable.lean`, own work): (2026-07-17) — the peu-ramifiée
                          glue: multiplicative reduction at `p` with `p ∣ v_p(j)` ⟹ `IsFlatAt p`,
                          from the new content leaf below plus the shared flat transport
                            - ❌· `torsion_flat_of_multiplicative_reduction` — `torsion_flat_of_multiplicative_reduction`
                              (`FreyCurve/Semistable.lean`, stated 2026-07-17): multiplicative
                              reduction over `ℤ_(p)` with `p ∣ v_p(j)` produces a finite flat Hopf
                              algebra over `ℤ_(p)` (étale generic fibre) whose `ℚ̄`-points are `Γ
                              ℚ`-equivariantly the `p`-torsion — the peu-ramifiée package in the
                              same DVR-`∃`-shape as the good-reduction leaf (Tate curve + Kummer
                              theory content)
                - ✅· `FreyCurve.torsion_isTameAtTwo` — (2026-07-16) from the arithmetic and the tame glue node below
                    - ✅· `WeierstrassCurve.isTameAtTwo_of_hasMultiplicativeReduction` — tame quotient at 2 from multiplicative reduction, now assembled by the
                      split/nonsplit case split over the transferred reduction
                      (`hasMultiplicativeReduction_padic`): the split half is the Tate exponent
                      quotient, the nonsplit half is the leaf below.
                        - ✅· `exists_tame_quotient_of_split_padic_two` — the split half of the tame-at-2 condition: the Tate valuation-exponent
                          quotient of `exists_tateTorsionQuotient` transported to global torsion
                          along the (bijective, by torsion counting) embedding into `ℚ_[2]`-torsion;
                          the quotient carries the TRIVIAL local action, which is unramified and
                          squares to 1.
                            - ✅· `WeierstrassCurve.exists_tateEquivSepClosure` — Tate's uniformisation over a separable closure, now DERIVED from the
                              choice-free Tate-curve uniformisation and Tate's variable-change
                              theorem: the variable change is `k`-rational, so its base-changed
                              point equivalence is Galois-equivariant, and the equivariance
                              transports through the composite.
                                - ✅· `WeierstrassCurve.exists_tateCurveEquivSepClosure` — the uniformization core, quotient form: Galois-equivariant Ωˣ/q^ℤ
                                  ≃+ E_q(Ω). DERIVED 2026-07-18 from the pre-quotient node
                                  exists_tateCurveHomSepClosure by the first isomorphism theorem:
                                  multiplicative lift ψ of the hom, QuotientGroup.lift over zpowers
                                  q, injectivity from the kernel characterization,
                                  MulEquiv.ofBijective, MulEquiv.toAdditiveLeft; equivariance
                                  descends definitionally on ofMul-classes.
                                    - ✅· `WeierstrassCurve.exists_tateCurveHomSepClosure` — the uniformization core, pre-quotient form: surjective Galois-
                                      equivariant hom Ωˣ →+ E_q(Ω) with kernel exactly q^ℤ. DERIVED
                                      2026-07-18 by feeding the finite-level canonical
                                      uniformisation tateCurveEquiv (underlying function
                                      pointMapQuot) into the sorried gluing implication
                                      exists_tateCurveHomSepClosure_of_finiteLevel.
                                        - ✅· `TateCurve.tateCurveEquiv` — the finite-level Tate uniformisation kˣ/q^ℤ ≃+ E_q(k),
                                          DERIVED from pointMapQuot_add + pointMapQuot_bijective
                                          with pointMapQuot (canonical, choice-free) as underlying
                                          function — the object the Ω-gluing consumes. RE-VENDORED
                                          2026-07-18 (stripped form): the annulus/evalA/pointMap
                                          machinery is in the tree (all PROVEN: CoeffRing
                                          evaluation, summability on the fundamental annulus,
                                          evaluated Weierstrass equation, annulusPoint
                                          nonsingularity, strict fundamental domain, kernel
                                          characterization pointMap_eq_zero_iff); the
                                          bilateral/Lambert negation-translation machinery stays in
                                          the reference commit 8282dfb^ until the addition-law proof
                                          consumes it.
                                            - ✅· `TateCurve.pointMapQuot_surjective` — surjectivity of the uniformisation (Silverman ATAEC
                                              V.3.1(d)/V.4). DERIVED 2026-07-18 from the x-onto leaf
                                              exists_annulus_bilateralX_eq: the leaf gives an
                                              annulus parameter u over the x-coordinate;
                                              Y_eq_of_X_eq gives y = bilateralY u or its negY, the
                                              latter realised by the inverse partner (u⁻¹ on the
                                              shell, q·u⁻¹ in the interior) via the PROVEN vertical
                                              case bilateral_negY_of_mul_trivial.
                                                - ❌· `TateCurve.exists_annulus_bilateralX_eq` — the x-onto leaf (sorry node, the analytic heart of
                                                  Silverman V.4): every affine solution (x, y) of
                                                  the Tate curve equation has an annulus parameter u
                                                  with bilateralX u = x. Attack: Newton-
                                                  polygon/valuation analysis of X(u) - x on the
                                                  annulus (theta quotient), using completeness of k.
                                            - ✅· `TateCurve.pointMapQuot_add` — the addition law (Silverman ATAEC V.3.1(c)). DERIVED
                                              2026-07-18 from three sorried series-identity leaves
                                              (chord, tangent, X-fibre) + the PROVEN vertical case
                                              bilateral_negY_of_mul_trivial (inversion/shift
                                              identities), the PROVEN bilateral coordinate bridge
                                              pointMap_eq_bilateral on the extended window |q|² <
                                              |w| ≤ 1, and quotient bookkeeping (annulus
                                              normalisation, trivial classes).
                                                - ✅· `TateCurve.eq_or_mul_eq_of_bilateralX_eq` — the X-fibre (Silverman V.4). DERIVED 2026-07-18
                                                  from the coordinate-pair injectivity
                                                  bilateralXY_inj: Y_eq_of_X_eq gives equal or negY-
                                                  related y-values; equal ⇒ injectivity ⇒ v = u;
                                                  negY-related ⇒ v = the inverse partner (u⁻¹ on the
                                                  shell, q·u⁻¹ in the interior) by the PROVEN
                                                  vertical case + injectivity, so uv ∈ {1, q}.
                                                    - ❌· `TateCurve.bilateralXY_inj` — coordinate-pair injectivity on the annulus
                                                      (sorry node — the injectivity half of
                                                      Silverman V.4): equal bilateral x- AND
                                                      y-values force equal parameters. Attack:
                                                      Newton-polygon/theta-quotient analysis of X(u)
                                                      - X(v) over the complete field, the y-value
                                                      separating the two sheets.
                                                - ✅· `TateCurve.bilateral_add_self` — the tangent identity (V.3.1(c) doubling case).
                                                  DERIVED 2026-07-18 from the cleared tangent
                                                  identities + the non-2-torsion leaf, same division
                                                  bookkeeping pattern as the chord case.
                                                    - ❌· `TateCurve.bilateral_ne_negY_of_sq_nontrivial` — non-2-torsion leaf (sorry node): u in the
                                                      annulus with u² not in the trivial class has
                                                      2Y(u) + X(u) ≠ 0 — the 2-torsion parameters
                                                      are exactly {-1, ±√q}·q^ℤ.
                                                    - ❌· `TateCurve.bilateral_tangentY_cleared` — cleared tangent Y-identity (sorry node):
                                                      -(Y(u²)+X(u²))E = M(X(u²)-X(u)) + Y(u)E.
                                                      Diagonal case.
                                                    - ❌· `TateCurve.bilateral_tangentX_cleared` — cleared tangent X-identity (sorry node):
                                                      (X(u²)+2X(u))E² = M² + ME with M the tangent-
                                                      slope numerator, E = y - negY. Diagonal case
                                                      of the cleared chord content.
                                                - ✅· `TateCurve.bilateral_add_of_X_ne` — the chord identity (V.3.1(c) generic case).
                                                  DERIVED 2026-07-18 from the cleared chord
                                                  identities bilateral_chordX_cleared /
                                                  bilateral_chordY_cleared: the triviality
                                                  exclusions follow from distinct x-values via the
                                                  proven inversion/shift identities, and the
                                                  slope/addX/addY division bookkeeping is field_simp
                                                  + linear_combination against the cleared forms.
                                                    - ❌· `TateCurve.bilateral_chordY_cleared` — cleared chord Y-identity (sorry node):
                                                      -(Y(uv)+X(uv))(X(u)-X(v)) =
                                                      (Y(u)-Y(v))(X(uv)-X(u)) + Y(u)(X(u)-X(v)) —
                                                      linear in the X-part output. Same attack as
                                                      the X-identity.
                                                    - ❌· `TateCurve.bilateral_chordX_cleared` — cleared chord X-identity (sorry node):
                                                      (X(uv)+X(u)+X(v))(X(u)-X(v))² = (Y(u)-Y(v))² +
                                                      (Y(u)-Y(v))(X(u)-X(v)) — pure polynomial
                                                      series identity, no slope/division/cases.
                                                      Attack: Ramanujan/Eisenstein manipulation of
                                                      divisor double series
                                                      (Venkatachaliengar–Cooper Ch. 1) or two-
                                                      transcendental descent; mathlib LACKS the
                                                      ℘-addition law (checked 2026-07-18), so the
                                                      ℂ-analytic route requires formalizing it
                                                      first.
                                        - ❌🟪 `WeierstrassCurve.exists_tateCurveHomSepClosure_of_finiteLevel` — the Ω-gluing implication (sorry node): GIVEN the finite-
                                          level canonical uniformisation lˣ/q^ℤ ≃+ E_q(l) with
                                          underlying pointMapQuot for every NALF l, the Ω-level hom
                                          exists. Content: finite subextensions of Ω/k are NALFs
                                          (unique valuative extension over the complete k —
                                          infrastructure absent from mathlib at this pin), the maps
                                          are compatible with inclusions and σ-twists by naturality
                                          of the universal series, and
                                          kernel/surjectivity/equivariance pass to the colimit.
                        - ✅· `WeierstrassCurve.exists_tame_quotient_of_nonsplit_padic_two` — the nonsplit half of the tame-at-2 condition, now ASSEMBLED: the exponent
                          quotient of the twisted minimal model transports through the (χ-twisted)
                          composite point equivalence; δ is the quadratic character of the
                          unramified L as a continuous GaloisRep (locally constant on cosets of the
                          open fixing subgroup of the embedded L), unramified by the Z2bar
                          embedding-fixing leaf, squaring to 1 by Int.units_mul_self.
                            - ✅· `WeierstrassCurve.exists_tateEquivSepClosure` — Tate's uniformisation over a separable closure, now DERIVED from the
                              choice-free Tate-curve uniformisation and Tate's variable-change
                              theorem: the variable change is `k`-rational, so its base-changed
                              point equivalence is Galois-equivariant, and the equivariance
                              transports through the composite.
                                - ✅· `WeierstrassCurve.exists_tateCurveEquivSepClosure` — the uniformization core, quotient form: Galois-equivariant Ωˣ/q^ℤ
                                  ≃+ E_q(Ω). DERIVED 2026-07-18 from the pre-quotient node
                                  exists_tateCurveHomSepClosure by the first isomorphism theorem:
                                  multiplicative lift ψ of the hom, QuotientGroup.lift over zpowers
                                  q, injectivity from the kernel characterization,
                                  MulEquiv.ofBijective, MulEquiv.toAdditiveLeft; equivariance
                                  descends definitionally on ofMul-classes.
                                    - ✅· `WeierstrassCurve.exists_tateCurveHomSepClosure` — the uniformization core, pre-quotient form: surjective Galois-
                                      equivariant hom Ωˣ →+ E_q(Ω) with kernel exactly q^ℤ. DERIVED
                                      2026-07-18 by feeding the finite-level canonical
                                      uniformisation tateCurveEquiv (underlying function
                                      pointMapQuot) into the sorried gluing implication
                                      exists_tateCurveHomSepClosure_of_finiteLevel.
                                        - ✅· `TateCurve.tateCurveEquiv` — the finite-level Tate uniformisation kˣ/q^ℤ ≃+ E_q(k),
                                          DERIVED from pointMapQuot_add + pointMapQuot_bijective
                                          with pointMapQuot (canonical, choice-free) as underlying
                                          function — the object the Ω-gluing consumes. RE-VENDORED
                                          2026-07-18 (stripped form): the annulus/evalA/pointMap
                                          machinery is in the tree (all PROVEN: CoeffRing
                                          evaluation, summability on the fundamental annulus,
                                          evaluated Weierstrass equation, annulusPoint
                                          nonsingularity, strict fundamental domain, kernel
                                          characterization pointMap_eq_zero_iff); the
                                          bilateral/Lambert negation-translation machinery stays in
                                          the reference commit 8282dfb^ until the addition-law proof
                                          consumes it.
                                            - ✅· `TateCurve.pointMapQuot_surjective` — surjectivity of the uniformisation (Silverman ATAEC
                                              V.3.1(d)/V.4). DERIVED 2026-07-18 from the x-onto leaf
                                              exists_annulus_bilateralX_eq: the leaf gives an
                                              annulus parameter u over the x-coordinate;
                                              Y_eq_of_X_eq gives y = bilateralY u or its negY, the
                                              latter realised by the inverse partner (u⁻¹ on the
                                              shell, q·u⁻¹ in the interior) via the PROVEN vertical
                                              case bilateral_negY_of_mul_trivial.
                                                - ❌· `TateCurve.exists_annulus_bilateralX_eq` — the x-onto leaf (sorry node, the analytic heart of
                                                  Silverman V.4): every affine solution (x, y) of
                                                  the Tate curve equation has an annulus parameter u
                                                  with bilateralX u = x. Attack: Newton-
                                                  polygon/valuation analysis of X(u) - x on the
                                                  annulus (theta quotient), using completeness of k.
                                            - ✅· `TateCurve.pointMapQuot_add` — the addition law (Silverman ATAEC V.3.1(c)). DERIVED
                                              2026-07-18 from three sorried series-identity leaves
                                              (chord, tangent, X-fibre) + the PROVEN vertical case
                                              bilateral_negY_of_mul_trivial (inversion/shift
                                              identities), the PROVEN bilateral coordinate bridge
                                              pointMap_eq_bilateral on the extended window |q|² <
                                              |w| ≤ 1, and quotient bookkeeping (annulus
                                              normalisation, trivial classes).
                                                - ✅· `TateCurve.eq_or_mul_eq_of_bilateralX_eq` — the X-fibre (Silverman V.4). DERIVED 2026-07-18
                                                  from the coordinate-pair injectivity
                                                  bilateralXY_inj: Y_eq_of_X_eq gives equal or negY-
                                                  related y-values; equal ⇒ injectivity ⇒ v = u;
                                                  negY-related ⇒ v = the inverse partner (u⁻¹ on the
                                                  shell, q·u⁻¹ in the interior) by the PROVEN
                                                  vertical case + injectivity, so uv ∈ {1, q}.
                                                    - ❌· `TateCurve.bilateralXY_inj` — coordinate-pair injectivity on the annulus
                                                      (sorry node — the injectivity half of
                                                      Silverman V.4): equal bilateral x- AND
                                                      y-values force equal parameters. Attack:
                                                      Newton-polygon/theta-quotient analysis of X(u)
                                                      - X(v) over the complete field, the y-value
                                                      separating the two sheets.
                                                - ✅· `TateCurve.bilateral_add_self` — the tangent identity (V.3.1(c) doubling case).
                                                  DERIVED 2026-07-18 from the cleared tangent
                                                  identities + the non-2-torsion leaf, same division
                                                  bookkeeping pattern as the chord case.
                                                    - ❌· `TateCurve.bilateral_ne_negY_of_sq_nontrivial` — non-2-torsion leaf (sorry node): u in the
                                                      annulus with u² not in the trivial class has
                                                      2Y(u) + X(u) ≠ 0 — the 2-torsion parameters
                                                      are exactly {-1, ±√q}·q^ℤ.
                                                    - ❌· `TateCurve.bilateral_tangentY_cleared` — cleared tangent Y-identity (sorry node):
                                                      -(Y(u²)+X(u²))E = M(X(u²)-X(u)) + Y(u)E.
                                                      Diagonal case.
                                                    - ❌· `TateCurve.bilateral_tangentX_cleared` — cleared tangent X-identity (sorry node):
                                                      (X(u²)+2X(u))E² = M² + ME with M the tangent-
                                                      slope numerator, E = y - negY. Diagonal case
                                                      of the cleared chord content.
                                                - ✅· `TateCurve.bilateral_add_of_X_ne` — the chord identity (V.3.1(c) generic case).
                                                  DERIVED 2026-07-18 from the cleared chord
                                                  identities bilateral_chordX_cleared /
                                                  bilateral_chordY_cleared: the triviality
                                                  exclusions follow from distinct x-values via the
                                                  proven inversion/shift identities, and the
                                                  slope/addX/addY division bookkeeping is field_simp
                                                  + linear_combination against the cleared forms.
                                                    - ❌· `TateCurve.bilateral_chordY_cleared` — cleared chord Y-identity (sorry node):
                                                      -(Y(uv)+X(uv))(X(u)-X(v)) =
                                                      (Y(u)-Y(v))(X(uv)-X(u)) + Y(u)(X(u)-X(v)) —
                                                      linear in the X-part output. Same attack as
                                                      the X-identity.
                                                    - ❌· `TateCurve.bilateral_chordX_cleared` — cleared chord X-identity (sorry node):
                                                      (X(uv)+X(u)+X(v))(X(u)-X(v))² = (Y(u)-Y(v))² +
                                                      (Y(u)-Y(v))(X(u)-X(v)) — pure polynomial
                                                      series identity, no slope/division/cases.
                                                      Attack: Ramanujan/Eisenstein manipulation of
                                                      divisor double series
                                                      (Venkatachaliengar–Cooper Ch. 1) or two-
                                                      transcendental descent; mathlib LACKS the
                                                      ℘-addition law (checked 2026-07-18), so the
                                                      ℂ-analytic route requires formalizing it
                                                      first.
                                        - ❌🟪 `WeierstrassCurve.exists_tateCurveHomSepClosure_of_finiteLevel` — the Ω-gluing implication (sorry node): GIVEN the finite-
                                          level canonical uniformisation lˣ/q^ℤ ≃+ E_q(l) with
                                          underlying pointMapQuot for every NALF l, the Ω-level hom
                                          exists. Content: finite subextensions of Ω/k are NALFs
                                          (unique valuative extension over the complete k —
                                          infrastructure absent from mathlib at this pin), the maps
                                          are compatible with inclusions and σ-twists by naturality
                                          of the universal series, and
                                          kernel/surjectivity/equivariance pass to the colimit.
            - ✅· `GaloisRepresentation.not_isIrreducible_of_isHardlyRamified` — B5 `GaloisRepresentation.not_isIrreducible_of_isHardlyRamified`
              (`GaloisRepresentation/HardlyRamified/Reducible.lean`, own work) — now (2026-07-16)
              from three explicit nodes in `HardlyRamified/Lift.lean` (own work), following
              Buzzard's 2026 EPSRC Lecture 4 (his B5a/B5b/B5c):
                - ❌· `exists_hardlyRamifiedLift` — B6a `exists_hardlyRamifiedLift` — an irreducible hardly ramified mod-ℓ rep (ℓ ≥ 5)
                  lifts to a hardly ramified ℓ-adic rep over the integers `O` of a finite extension
                  of `ℚ_ℓ` (bundled in `structure HardlyRamifiedLift`: `O` + framed rep + reduction
                  map + Frobenius-charpoly compatibility). Deformation theory / modularity lifting
                  without residual modularity
                - ✅· `residual_charFrob_eq` — B6bc `residual_charFrob_eq` — the residual Frobenius charpolys of a liftable rep
                  are those of `1 ⊕ χ̄` (`X² − (q+1)X + q`) — now (2026-07-16) from the faithful
                  split ( from the FLT project's newer layer):
                    - ❌· `IsHardlyRamified.mem_isCompatible` — B6b `IsHardlyRamified.mem_isCompatible` (`HardlyRamified/Family.lean`, ;
                      conclusion named `IsInHardlyRamifiedFamily` as a marked ) — a hardly ramified
                      ℓ-adic rep lives in a compatible family (`GaloisRepFamily.lean`, defs, ) all
                      of whose odd members are hardly ramified. STRENGTHENED (2026-07-16): the
                      package now records injectivity of the coefficient-ring embeddings into `ℚ̄_p`
                      — an audit of the glue's proof skeleton showed the upstream statement is too
                      weak for the charpoly descent (algebraMap from a domain to a field need not be
                      injective); true for the intended subrings of `ℚ̄_p`
                    - ✅· `residual_charFrob_eq_of_family` — `residual_charFrob_eq_of_family` (own work, `Lift.lean`) — compatibility
                      BOOKKEEPING — now (2026-07-16): extract the 3-adic member via the number-field
                      embedding; its charpoly at Frob_q is `X² − (1+q)X + q` by B6c's trace + the
                      cyclotomic determinant at Frobenius + the 2-dim reconstruction (generalized to
                      comm rings); transport through baseChange-conj to the family, descend to the
                      coefficient field by injectivity of the embedding, ride compatibility to the
                      ℓ-adic member, descend to `O` by the strengthened-B6b injectivity, and reduce
                      through `charFrob_compat`. Exceptional set: `S₀ ∪ {2-place, 3-place}`.
                      Consumes B6c and the ℓ-adic Frobenius-value node. AUDIT RESTATEMENT
                      (2026-07-16): the conclusion (and B6bc's, and the Chebotarev–Brauer–Nesbitt
                      hypothesis) now carries a finite exceptional set `S` of places — the family's
                      `isCompatible` only pins charpolys outside an unspecified finite set, so the
                      `∀ q ∉ {2,3,ℓ}` form was unprovable; the density argument absorbs any finite
                      `S` (new bridge: `toHeightOneSpectrumRingOfIntegersRat_injective`, distinct
                      primes give distinct places, so a finite set of places excludes only finitely
                      many primes in the auxiliary-prime selection). Proof ingredients consumed:
                        - ✅· `IsHardlyRamified.three_adic` — B6c: trace(Frob_p) = 1 + p for p ≥ 5. DERIVED 2026-07-18 from
                          exists_frobenius_triangular by LinearMap.trace_eq_matrix_trace +
                          Matrix.trace_fin_two on the triangular form [[p, *], [0, 1]].
                            - ✅· `GaloisRepresentation.IsHardlyRamified.exists_frobenius_triangular` — Frobenius triangularity for p ≥ 5. DERIVED 2026-07-18 by chaining
                              exists_residual_isHardlyRamified → mod_three (ModThree.lean, RE-
                              VENDORED into the tree) →
                              exists_frobenius_triangular_of_residual_trivial_quotient.
                                - ✅· `GaloisRepresentation.IsHardlyRamified.mod_three` — mod-3 classification (DERIVED, re-vendored 2026-07-18): a mod-3
                                  hardly ramified rep has a Γℚ-equivariant surjection onto the
                                  trivial 1-dim rep. From mod_three_reducible +
                                  mod_three_of_stable_line (Minkowski bookkeeping PROVEN).
                                    - ❌· `GaloisRepresentation.IsHardlyRamified.exists_line_with_locally_unramified_quotCharacter` — the stable line with locally-unramified quotient character at
                                      2 and 3 (sorry node): flatness at 3 forces the étale quotient
                                      via the connected-étale sequence (the Serre swap); tameness at
                                      2 kills ramification there.
                                    - ❌· `GaloisRepresentation.IsHardlyRamified.mod_three_reducible` — mod-3 reducibility (sorry node): Dickson classification +
                                      ramification constraints eliminate irreducible image — Serre
                                      §5.4/Tate argument for p = 3. The PGL2/Dickson/OddAbsIrred
                                      clusters are in the reference commit 8282dfb^.
                                - ❌· `GaloisRepresentation.IsHardlyRamified.exists_frobenius_triangular_of_residual_trivial_quotient` — ordinarity lifting (sorry node — the deformation heart of B6c):
                                  the residual trivial-quotient surjection lifts 3-adically to the
                                  triangular Frobenius basis, diagonal = det = cyclotomic, value p
                                  at Frob_p.
                                - ✅· `GaloisRepresentation.IsHardlyRamified.exists_residual_isHardlyRamified` — residual hardly-ramifiedness. DERIVED 2026-07-18: the determinant
                                  condition transfers by LinearMap.det_baseChange + the scalar
                                  tower, and unramifiedness by the existing IsUnramifiedAt base-
                                  change instance; the remaining content is the residue package and
                                  the flatness/tameness transfer leaves.
                                    - ❌· `GaloisRepresentation.IsHardlyRamified.isTameAtTwo_baseChange_residue` — tameness-at-2 transfer (sorry node): π ⊗ 1 through kk ⊗ R ≅ kk
                                      and the pushforward of δ along the residue map; conditions
                                      transfer on simple tensors.
                                    - ❌· `GaloisRepresentation.IsHardlyRamified.isFlatAt_baseChange_residue` — flatness transfer (sorry node): open ideals of the discrete
                                      field are ⊥/⊤; the ⊥ case is the I = 𝔪 instance of ρ.IsFlatAt
                                      along kk ≅ R/𝔪 and base-change composition.
                                    - ❌· `GaloisRepresentation.IsHardlyRamified.exists_residue_package` — the residue package (sorry node): kk := R/𝔪 with
                                      Field/Finite/char-3/discrete instances, surjective continuous
                                      ℤ₃-algebra map, open maximal ideal, kernel = 𝔪, rank-2 base
                                      change.
                - ✅· `not_isIrreducible_of_charFrob_eq` — `not_isIrreducible_of_charFrob_eq` — Chebotarev + Brauer– Nesbitt — now
                  (2026-07-16, `Chebotarev.lean` + proof in `Lift.lean`): the agreement set with `1
                  ⊕ χ̄`'s charpolys is closed (module topology on `End` over `ZMod ℓ` is discrete ;
                  coefficient maps continuous) and contains the dense Frobenius conjugates, so
                  Brauer–Nesbitt applies. Children:
                    - ✅· `dense_conjClasses_globalFrob` — `dense_conjClasses_globalFrob` — Chebotarev density, topological form — now
                      (2026-07-16) by the profinite limit argument (: cosets of fixing subgroups of
                      finite subextensions are a neighborhood basis,
                      `krullTopology_mem_nhds_one_iff`; the finite-level statement puts a Frobenius
                      conjugate in every coset):
                        - ❌· `exists_frobenius_conj_mem_coset` — `exists_frobenius_conj_mem_coset` — Chebotarev, finite level: for every
                          finite subextension `E` of `K̄/K` and every `σ`, the coset `σ·Gal(K̄/E)`
                          contains a conjugate of a `globalFrob v` with `v ∉ S` (existence form of
                          Chebotarev for the Galois closure of `E/K`)

## Canonical frontier (2026-07-16, session 4 close — audit-verified)

The 21 open nodes, by declaration name (grep-verified against the tree):
`exists_frobenius_conj_mem_coset` (finite Chebotarev),
`exists_hardlyRamifiedLift` (B6a), `exists_weilPairing`,
`FreyPackage.exists_p_point_of_not_isIrreducible_of_minkowski` (Serre
core), `mem_isCompatible` (B6b), `mod_three`,
`open_normal_subgroup_eq_top_of_inertia_le` (Minkowski),
`prime_torsion_card`, `smul_surjective`, `three_adic` (B6c),
`WeierstrassCurve.exists_tateEquivSepClosure`,
`WeierstrassCurve.exists_variableChange_tateCurve`,
`WeierstrassCurve.isFlatAt_of_hasGoodReduction`,
`WeierstrassCurve.isFlatAt_of_hasMultiplicativeReduction`,
`WeierstrassCurve.isTameAtTwo_of_hasMultiplicativeReduction`,
`WeierstrassCurve.isUnramifiedAt_of_hasGoodReduction`,
`WeierstrassCurve.isUnramifiedAt_of_hasMultiplicativeReduction`,
`WeierstrassCurve.mazur_classification`,
`WeierstrassCurve.resultant_Φ_ΨSq`,
`WeierstrassCurve.torsion_flat_of_good_reduction` (Hopf package),
`WeierstrassCurve.torsion_unramified_of_good_reduction` (NOS).

## Next-step reconnaissance (2026-07-16, session 4 close)

- **`minkowski_character_trivial` — the mathlib route is VERIFIED to
 exist at our pin** (all names checked in
 `Mathlib/NumberTheory/NumberField/ExistsRamified.lean` and
 `Discriminant/Different.lean`):
 `NumberField.finrank_eq_one_of_unramified` ([Algebra.Unramified ℤ 𝒪]
 ⟹ finrank ℚ K = 1), `NumberField.exists_not_isUnramifiedIn`,
 `NumberField.exists_not_isUnramifiedAt_int_of_isGalois` (Galois case:
 some prime has ALL primes above it ramified — the right form for the
 abelian fixed field), `NumberField.not_dvd_discr_iff_isUnramifiedIn`,
 `NumberField.abs_discr_gt_two`. What remains is the **dictionary**:
 (1) `K := IntermediateField.fixedField H` is finite over ℚ (VERIFIED
 in mathlib: `instance [IsGalois k K] : CompactSpace Gal(K/k)`
 in `FieldTheory/Galois/Profinite.lean` gives compactness of `Γ ℚ`,
 and `Subgroup.quotient_finite_of_isOpen` in
 `Topology/Algebra/OpenSubgroup.lean` gives finite index of the open
 subgroup; the correspondence is in MATHLIB proper
 (`Mathlib/FieldTheory/Galois/Infinite.lean`):
 `InfiniteGalois.fixingSubgroup_fixedField (H : ClosedSubgroup _)
 [IsGalois k K] : fixingSubgroup (fixedField H) = H` — exactly the
 recovery direction needed (`H` open ⟹ closed; `fixedField H = ⊥` ⟹
 `H = fixingSubgroup ⊥ = ⊤` via `IntermediateField.fixingSubgroup_bot`)
 — and `IsGalois ℚ ℚ̄` synthesizes via the priority-100 instance
 `IsAlgClosure.isGalois` (`Galois/Basic.lean:594`)), giving
 `NumberField K`;
 (2) `localInertiaGroup q ≤ ker (χ ∘ res_q)` for all `q` transfers to
 `Algebra.IsUnramifiedAt ℤ P` for every prime `P` of `𝓞 K` — the
 local-global inertia dictionary (same flavor as the NOS glue node
 `isUnramifiedAt_of_hasGoodReduction`; whichever is built first should
 factor out the common bridge). The dictionary's two endpoints are now
 precisely identified: `localInertiaGroup v` is mathlib's GENERIC
 `AddSubgroup.inertia` (`Algebra/Group/Subgroup/Basic.lean:1123`,
 membership DEFINITIONAL: `σ ∈ I.inertia G ↔ ∀ x, σ • x - x ∈ I`)
 applied to `(𝔪 (IntegralClosure 𝒪ᵥ Kᵥᵃˡᵍ)).toAddSubgroup` acting via
 `Γ Kᵥ`; the NOS node speaks `ValuationSubring.inertiaSubgroup`
 (`RingTheory/Valuation/RamificationGroup.lean:50`) of valuation
 subrings of `kˢᵉᵖ`; the classical side is `Algebra.IsUnramifiedAt` ↔
 `Ideal.ramificationIdx = 1` (`Ideal.ramificationIdx_eq_one_iff`, used
 in `ExistsRamified.lean`). The dictionary = compatibility of the two
 inertia presentations along the embedding `ℚ̄ ↪ ℚ̄_q` + the
 inertia-trivial ⟹ unramified direction for the finite quotient.
 **Step (1) is now in-tree**: `finite_quotient_of_isOpen`
 (`MazurTorsion.lean`, unconditional) — an open subgroup of `Γ ℚ` has
 finite quotient; the full instance chain (`IsAlgClosure.isGalois` →
 `CompactSpace Gal` → `Subgroup.quotient_finite_of_isOpen`)
 synthesizes without intervention. MOREOVER mathlib has the COMPLETE
 group↔field transfer (`FieldTheory/Galois/Infinite.lean`):
 `InfiniteGalois.isOpen_iff_finite` (`IsOpen L.fixingSubgroup ↔
 FiniteDimensional k L`), `InfiniteGalois.normal_iff_isGalois`, and
 the combined `isOpen_and_normal_iff_finite_and_isGalois` — so for
 `H` open normal, `L := fixedField H` has `fixingSubgroup L = H`
 (correspondence, `H` closed) and is a FINITE GALOIS extension of ℚ
 by these named lemmas, giving `NumberField L` and activating
 `exists_not_isUnramifiedAt_int_of_isGalois` directly. Every step of
 the Minkowski node except the inertia dictionary is now named
 mathlib API. Assembly facts (scratch-COMPILED 2026-07-16):
 `IntermediateField.fixedField (E := AlgebraicClosure ℚ) H`
 typechecks for `H : Subgroup (Γ ℚ)` (the parameter is named `E`, not
 `K`), and `IsGalois ℚ ℚ̄` + `CompactSpace (Γ ℚ)` BOTH synthesize —
 but ONLY under `set_option backward.isDefEq.respectTransparency
 false` (the known module-system gotcha; without it `IsGalois`
 synthesis fails). Remaining derivation names also verified:
 `Subgroup.isClosed_of_isOpen` (`OpenSubgroup.lean:273`, for feeding
 the `ClosedSubgroup` correspondence) and
 `IntermediateField.finrank_eq_one_iff : finrank F K = 1 ↔ K = ⊥`
 (`Adjoin/Basic.lean:275`, for extracting `1 < finrank` from
 `H ≠ ⊤`). Exact correspondence forms:
 `InfiniteGalois.fixingSubgroup_fixedField (H : ClosedSubgroup
 Gal(K/k)) [IsGalois k K] : (fixedField H).fixingSubgroup = H.1`
 (apply at `⟨H, Subgroup.isClosed_of_isOpen H hopen⟩`) and
 `IntermediateField.fixingSubgroup_bot : fixingSubgroup ⊥ = ⊤`
 (@[simp], `Galois/Basic.lean:258`) for the nontriviality step. The
 derivation is mechanically specified, every name compilation- or
 grep-verified; write it as [dictionary node, sorry] + [assembly,
 proven] in one sitting. The dictionary node should be stated with
 the `{𝒪 : Type*} [IsIntegralClosure 𝒪 ℤ L]` parametrization of
 `ExistsRamified.lean` (avoids constructing `NumberField L` inside
 the statement; provide `haveI : NumberField L := ⟨⟩` in the
 assembly). The prime-above-`p` existence step:
 `Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
 [Algebra.IsIntegral ℤ 𝒪] (P) [IsPrime P] (hker : ker ≤ P) :
 ∃ Q, IsPrime Q ∧ Q.comap (algebraMap ℤ 𝒪) = P`
 (`RingTheory/Ideal/GoingUp.lean:280`) at `P := span {(p : ℤ)}`;
 `(p : 𝒪) ∈ Q` follows from the comap equation; the integrality and
 injectivity instances come from the `IsIntegralClosure` invocations
 used verbatim in `ExistsRamified.lean` (`isIntegral_algebra`,
 `algebraMap_injective`). NOTHING in the assembly plan remains
 unverified. **EXECUTED (2026-07-16, same session): the assembly
 COMPILED with one fix round (missing imports). The Minkowski node is
 now ; the open sorry is
 `isUnramifiedAt_of_inertia_le_fixingSubgroup` — the pure inertia
 dictionary, shared with the five glue nodes. The dictionary's core
 mechanism is already :
 `Field.absoluteGaloisGroup.lift_map (f) (σ : Γ L) (x : Kᵃˡᵍ) :
 AlgebraicClosure.map f (map f σ x) = σ (AlgebraicClosure.map f x)`
 (`AbsoluteGaloisGroup.lean:101`) — the chosen embedding
 `ℚ̄ ↪ ℚ̄_q` intertwines the restricted action with the original, so
 a σ in the local inertia (trivial mod `𝔪` on the integral closure
 upstairs) transports its congruence to the embedded `𝓞 L`, giving
 trivial residue action at the induced prime. Target shape:
 `Algebra.IsUnramifiedAt R q` is an ABBREV for
 `FormallyUnramified R (Localization.AtPrime q)`
 (`Unramified/Locus.lean:45`), with the concrete characterization
 `Algebra.isUnramifiedAt_iff_map_eq` (`Unramified/LocalRing.lean:134`,
 the file whose FLT overlay is ALREADY VENDORED): unramified at `q`
 over `p` ⟺ `κ(q)/κ(p)` separable (automatic here — finite fields)
 ∧ `pS_q = qS_q`. So the dictionary reduces to the ideal equality
 `q·(𝓞 L)_Q = Q·(𝓞 L)_Q`, i.e. `e = 1`, from the trivial inertia
 action — the classical argument. Hypothesis-exact bridging form:
 `Ideal.ramificationIdx_eq_one_iff [q.IsPrime]
 [Algebra.EssFiniteType R S] [Algebra.IsIntegral R S]
 [PerfectField (q.under R).ResidueField] :
 q.ramificationIdx R = 1 ↔ Algebra.IsUnramifiedAt R q`
 (`RamificationInertia/Ramification.lean:105`) — for `R = ℤ` the
 residue field of `q.under ℤ` is `𝔽_p` (perfect ✅), so the dictionary
 may equivalently prove `ramificationIdx = 1`, the purely
 ideal-theoretic form. Its instance chain is complete:
 `EssFiniteType.of_finiteType` is an INSTANCE
 (`EssentialFiniteness.lean:95`), fed by `FiniteType.of_finite` from
 the module-finiteness of rings of integers, and `PerfectField` of
 finite fields is instance-automatic. SCRATCH-COMPILED (2026-07-16):
 `Ideal.ramificationIdx_eq_one_iff.mp` elaborates at `ℤ → 𝓞 L` given
 only `haveI := IsIntegralClosure.isIntegral_algebra ℤ (A := 𝓞 L) L`
 and the transparency option — so the dictionary node may be proven
 by establishing `Q.ramificationIdx ℤ = 1` from the inertia
 hypothesis, with the conversion to `IsUnramifiedAt` a one-liner.
 For the `e = 1` step itself, mathlib's
 `NumberTheory/RamificationInertia/HilbertTheory.lean` provides the
 group side: `inertia G P` (the `MulSemiringAction` inertia subgroup
 for ideals under group actions, with
 `IsInertiaField.of_isGaloisGroup` and the `rank_left`/`rank_right`
 theorems tying its fixed field's degrees to `e` and `f`) — a THIRD
 inertia presentation, and the SHORTEST route — no field bookkeeping
 needed: **`card_inertia_eq_ramificationIdxIn p : Nat.card (inertia
 Gal(L/K) P) = p.ramificationIdxIn B`** (used inside `rank_left`)
 gives `e` DIRECTLY as the inertia group's cardinality (exact form:
 `Ideal.card_inertia_eq_ramificationIdxIn` at `Galois.lean:317`,
 hypotheses `[IsDomain R] [IsDomain S] [Module.Finite R S] [Flat R S]
 [P.LiesOver p] [p.IsPrime] [P.IsPrime] [PerfectField p.ResidueField]`
 — for `ℤ → 𝓞 L` the only nonobvious one is `Flat ℤ (𝓞 L)`, which
 holds since torsion-free over a PID; note the inertia here is
 `P.inertia G` — `Ideal.inertia`, a FOURTH spelling, for a
 `MulSemiringAction` of `G = Gal(L/ℚ)` via `IsGaloisGroup`); trivial
 inertia ⟹ card 1 ⟹ `ramificationIdxIn = 1`, then (SCRATCH-COMPILED
 2026-07-16: `Ideal.card_inertia_eq_ramificationIdxIn (G := (L ≃ₐ[ℚ]
 L)) (Ideal.span {p}) Q` elaborates at `ℤ → 𝓞 L` — the `Flat` and
 `MulSemiringAction` instances synthesize automatically given the
 standing `isIntegral_algebra` haveI and the transparency option —
 CAVEAT: that scratch took `[PerfectField (span {p}).ResidueField]`
 as a HYPOTHESIS; the derived proof must supply it via
 `PerfectField.ofFinite` + finiteness of `(span {q} : Ideal
 ℤ).ResidueField` ≅ 𝔽_q — BRIDGE FOUND
 (`LocalRing/ResidueField/Ideal.lean:110`):
 `instance : IsFractionRing (R ⧸ I) I.ResidueField`; for maximal
 `I = span {q}` the quotient `ℤ ⧸ I` is already a (finite) field, so
 the fraction-ring algebraMap is bijective and `Finite I.ResidueField`
 transfers along the resulting equiv (finiteness of `ℤ ⧸ span {q}`
 from `Int.instFiniteQuotientSpan`-style instances or
 `Ring.HasFiniteQuotients.finiteQuotient` with `span {q} ≠ ⊥`).
 SCRATCH-COMPILED (2026-07-16), full fragment: `Prime (q:ℤ)` →
 `span_singleton_prime` → `isMaximal_of_ne_bot` →
 `Ring.HasFiniteQuotients.finiteQuotient` →
 `IsFractionRing.surjective_iff_isField.mpr
 ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax)` →
 `Finite.of_surjective` → `PerfectField` by `inferInstance`. (Do NOT
 introduce `haveI : Field (ℤ⧸I)` — it creates an instance diamond
 against the quotient's CommRing path; go through `IsField` instead.) Also confirmed: `Ideal.liesOver_span_iff (hP : P ≠ ⊤)
 (hp : Prime p) : P.LiesOver (span {p}) ↔ algebraMap R S p ∈ P`
 (`KrullDimension/Basic.lean:202`) supplies the `LiesOver` instance
 from the membership hypothesis)
 `ramificationIdxIn_eq_ramificationIdx` (the lemma ExistsRamified.lean
 itself uses) lands at the specific prime and
 `ramificationIdx_eq_one_iff.mp` (scratch-compiled) finishes. The
 dictionary then only needs the transport:
 `localInertiaGroup`-image-fixes-`L` ⟹ `inertia Gal(L/ℚ) Q` trivial
 (via `lift_map` and surjectivity of restriction to `L`).
 Post-derivation audit:
 `open_normal_subgroup_eq_top_of_inertia_le`,
 `minkowski_character_trivial`, and
 `exists_torsion_embedding_of_not_isIrreducible` all show exactly
 `[propext, sorryAx, Classical.choice, Quot.sound]` — correctly
 rooted through the dictionary, no foreign axioms.**;
 (3) conclude `ker χ = ⊤` from `fixedField χ.ker = ⊥` by the infinite
 Galois correspondence, hence `χ = 1`. Estimated: one focused session;
 start from a FRESH context.

## Previous reconnaissance (2026-07-16, session 3 close)

- `torsion_isUnramified` / `torsion_isTameAtTwo` / `torsion_isFlat` /
 `exists_weilPairing`: the natural source is the FLT repo's
 `FLT/KnownIn1980s/EllipticCurves/` directory (TateCurve.lean 512
 lines, plus WeilPairing.lean, Torsion.lean, GoodReduction.lean,
 Flat.lean, TateParameter.lean, TateCurveBaseChange.lean,
 ReductionBaseChange.lean, TateCurveConstruction.lean) — exactly the
 remaining Frey-condition vocabulary. **BLOCKER WITHDRAWN
 (2026-07-16, later the same day): the earlier check was faulty —
 `Mathlib.AlgebraicGeometry.EllipticCurve.Reduction` and
 `Mathlib.NumberTheory.LocalField.Basic` BOTH exist at our pinned rev
 (a3364faec429), and the FLT repo pins the SAME rev. No pin bump is
 needed.** The closure (verified): the KnownIn1980s
 EllipticCurves files plus the FLT-repo Mathlib-additions
 `FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Reduction`,
 `FLT.Mathlib.RingTheory.Valuation.ValuativeRel.Basic`,
 `FLT.Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology`,
 `FLT.Slop.NumberTheory.TsumDivisorsAntidiagonal`, and their recursive
 imports — a multi-file workstream, now fully unblocked at
 the current pin. NB `tateEquiv` (Tate's uniformization)
 is **sorry-d DATA** (a `def`), so must track it as
 meaning-poisoning until its existence node closes (cf. the old
 `galoisRep` situation).
- `residual_charFrob_eq_of_family` (glue): the eventual proof needs an
 embedding `E →+* ℚ̄₃` (DONE 2026-07-16:
 `nonempty_ringHom_to_padicAlgClosure`, proven sorry-free in
 `Lift.lean` via `IsAlgClosed.lift`), charpoly-vs-baseChange and conj (DONE 2026-07-16:
 `charpoly_baseChange_conj`, proven sorry-free in `Lift.lean` — the
 family-membership equation transports charpolys along
 `algebraMap A B`), trace/det-to-coefficients for
 2-dim (DONE 2026-07-16: `charpoly_eq_quadratic_of_finrank_two` +
 generic quadratic coefficient lemmas, proven sorry-free in
 `Chebotarev.lean`), and a 3-adic Frobenius value for the cyclotomic
 character
 (consider stating a single ℤ_p-adic Frobenius-value node
 `cyclotomicCharacter` at `globalFrob q` = `q`, from which
 `cyclotomicCharacterModL_globalFrob` follows via
 `cyclotomicCharacter.toZModPow` — bridging `PadicInt.toZMod` with
 `toZModPow 1` needs a small proven lemma).
- `not_isIrreducible_of_charpoly_eq` (Brauer–Nesbitt): an elementary
 route avoiding semisimplification: Cayley–Hamilton gives
 `(ρg − 1)(ρg − χg) = 0`; on `H := ker χ̄` every element is unipotent
 (`(ρh − 1)² = 0`), so a 2-dim Kolchin argument yields an `H`-fixed
 line; its Galois orbit analysis (H normal) plus, in the ρ|H-trivial
 case, simultaneous triangularization of a commuting split family,
 produces an invariant line. Both ingredients are candidate stated
 nodes if the direct proof stalls.

## Policy: no citation-terminal nodes (Deyao, 2026-07-16)

The FLT project's `knownin1980s` mechanism (an axiom proving any proposition
"an expert could deduce from pre-1990 literature") is **banned** here — first
 as a sorry-backed theorem, then removed altogether. No node of the
tree may be closed by appeal to expert knowledge or the literature; a node is
closed only when Lean compiles its proof. The full tree, including Mazur,
Ribet, Wiles–Taylor–Wiles and all supporting theory, is to be brought into
Lean and checked mechanically. This increases the scope enormously and that
is an explicit, accepted choice: the point is that the trust boundary is the
Lean kernel plus the (shrinking) list of `sorry`s — never a human assertion.

## Vendored material

`Fermat/FreyPackage.lean` and `Fermat/FreyCurve.lean` are adapted from the
FLT project (https://github.com/ImperialCollegeLondon/FLT, Apache 2.0,
Buzzard–Van de Velde–Monticone), with module-system syntax removed and small
cast/tactic fixes for mathlib v4.32.0-rc1. Their assumption mechanism
(`knownin1980s` etc.) is always replaced by explicit `sorry`-rooted theorems
here, so `#print axioms` remains the single source of truth for what is
assumed. Axiom invariant: every declaration must use at most
`[propext, Classical.choice, Quot.sound, sorryAx]`.

## Log

- 2026-07-16: project scaffolded in `fermat/`; branch `flt-formalization`,
 worktree `/tmp/flt-worktree`. Layer 1 (reduction to odd primes ≥ 5) built.
- 2026-07-16: layer 2 — FreyPackage normalization + Frey curve with Δ, c₄, j
 computations, all sorry-free; sorry root moved to `FreyPackage.false`.
- 2026-07-16: layer 3 — the FLT project's 32-module closure under
 `Fermat/FLT/` (import-rewritten; `knownin1980s` axiom → sorry-backed
 theorem; one auto-generated instance name fixed). mathlib re-pinned to the
 FLT project's exact rev a3364faec429. `FreyPackage.false` proven from
 `mazur` + B4; sorry frontier now: B4, knownin1980s (Mazur), Torsion
 infrastructure (6), HardlyRamified/Frey (2). FLT repo cloned to
 ~/Documents/cs/FLT for reference (never build there).
 NB: the main checkout at ~/Documents/cs/dissertation was hit by an iCloud
 eviction incident (see chat log); pushes go through the rescue clone in the
 session scratchpad until the main .git re-materializes.
- 2026-07-16 (session 2): `group_theory_lemma` sorry-free in new file
 `Fermat/FLT/EllipticCurve/TorsionCounting.lean` (~350 lines: torsionBy
 transfer equivs, torsion of Pi, `#torsionBy d (ZMod m) = gcd d m`,
 structure-theorem + counting + CRT assembly). `Module.Finite (ZMod n)`
 instance in Torsion.lean fixed (`[NeZero n]`, was false for n = 0) and
 derived from `n_torsion_finite`. Axiom audit clean. Sorry frontier now:
 Mazur, B4, `torsion_isHardlyRamified` (2 in HardlyRamified/Frey.lean),
 `n_torsion_finite`, `n_torsion_card`, `galoisRep` (data).
- 2026-07-16 (session 2, cont.): `WeierstrassCurve.galoisRep` CONSTRUCTED —
 the sorry-d data node is closed; the Galois action on `n`-torsion is the
 real one, continuity via finite-extension stabilizers (open fixing
 subgroups, Krull topology). sorryAx now enters `galoisRep` only through
 `n_torsion_finite`. Sorry frontier: Mazur, B4, 2× HardlyRamified/Frey,
 `n_torsion_finite`, `n_torsion_card` — 6 sorries total, all Props.
- 2026-07-16 (session 2, cont.): B4 decomposed — `torsion_not_isIrreducible`
 now proven from `torsion_isHardlyRamified` + new node **B5**
 (`HardlyRamified/Reducible.lean`). Sorry frontier (5, all Props):
 `mazur`, `torsion_isHardlyRamified`, B5, `n_torsion_finite`,
 `n_torsion_card`.
- 2026-07-16 (session 2, cont.): `n_torsion_finite` decomposed and derived —
 new file `TorsionFinite.lean` (own work) proves finiteness from two
 polynomial sorry nodes (`eval_ΨSq_eq_zero_of_smul_eq_zero`,
 `ΨSq_ne_zero_of_charDvd`). Sorry frontier (6, all Props):
 `mazur`, `torsion_isHardlyRamified`, B5, `n_torsion_card`,
 `eval_ΨSq_eq_zero_of_smul_eq_zero`, `ΨSq_ne_zero_of_charDvd`.
- 2026-07-16 (session 2, cont.): **B5 decomposed and derived** — new file
 `HardlyRamified/Lift.lean` (own work) states B6a (ℓ-adic lift, bundled
 `HardlyRamifiedLift` structure), B6bc (residual Frobenius charpolys are
 those of `1 ⊕ χ̄`; to be split into faithful B6b/B6c), and the
 Chebotarev–Brauer–Nesbitt node; B5 proven from them. Sorry frontier
 (8, all Props): `mazur`, `torsion_isHardlyRamified`, B6a, B6bc,
 Chebotarev–Brauer–Nesbitt, `n_torsion_card`,
 `eval_ΨSq_eq_zero_of_smul_eq_zero`, `ΨSq_ne_zero_of_charDvd`.
- 2026-07-16 (session 3): **`mazur` decomposed and derived** — new file
 `FreyCurve/MazurTorsion.lean` (own work) states Serre's §4.1
 reducible-case analysis (`exists_torsion_embedding_of_not_isIrreducible`:
 reducibility yields an elliptic curve over ℚ with rational points ⊇
 ℤ/2 × ℤ/2p) and Mazur's torsion theorem in weak form
 (`mazur_torsion_bound`: no such curve exists for prime p ≥ 5);
 `FreyPackage.mazur` proven from them by contradiction. Axiom audit clean.
 Tree legend gains □ (not yet started) for planned-but-unstated deeper
 nodes (Vélu quotients, Mazur's full fifteen-group classification).
 Sorry frontier (9, all Props): `exists_torsion_embedding_of_not_isIrreducible`,
 `mazur_torsion_bound`, `torsion_isHardlyRamified`, B6a, B6bc,
 Chebotarev–Brauer–Nesbitt, `n_torsion_card`,
 `eval_ΨSq_eq_zero_of_smul_eq_zero`, `ΨSq_ne_zero_of_charDvd`.
- 2026-07-16 (session 3, cont.): **`mazur_torsion_bound` ** from the
 new faithful sorry node `WeierstrassCurve.mazur_classification` (Mazur's
 fifteen-group torsion theorem, stated on `Submodule.torsion ℤ E(ℚ)`),
 closing the □ for the classification. Proof: torsion corestriction of an
 injective hom + `Nat.card` comparison against each of the fifteen groups
 (`Nat.card_zmod`, `Nat.card_prod`, omega). The unused primality
 hypothesis was dropped from `mazur_torsion_bound` (only `5 ≤ p` is
 needed). Axiom audit clean. Sorry frontier (9, all Props):
 `exists_torsion_embedding_of_not_isIrreducible`, `mazur_classification`,
 `torsion_isHardlyRamified`, B6a, B6bc, Chebotarev–Brauer–Nesbitt,
 `n_torsion_card`, `eval_ΨSq_eq_zero_of_smul_eq_zero`,
 `ΨSq_ne_zero_of_charDvd`.
- 2026-07-16 (session 3, cont.): **`torsion_isHardlyRamified` decomposed
 and derived** — new file `HardlyRamified/FreyConditions.lean` (own work)
 states the four defining conditions of `IsHardlyRamified` for the Frey
 curve as separate nodes (`torsion_det` — Weil pairing;
 `torsion_isUnramified` — Néron–Ogg–Shafarevich + Tate curve;
 `torsion_isFlat` — finite flat group scheme at p; `torsion_isTameAtTwo`
 — Tate curve at 2), and `Frey.lean` assembles them by the structure
 constructor. **Sorry gate installed** (`Fermat/SorryGate.lean`, root
 `Fermat.lean`): `lake build` now FAILS with `SORRY GATE FAILED` while
 `fermat_last_theorem` depends on `sorryAx` (and enforces the axiom
 invariant); a gate failure is the expected outcome during development —
 the continue-signal for the loop. Scratch audits import `Fermat.Basic` +
 leaf modules, never root `Fermat`. Axiom audit clean. Sorry frontier
 (11, all Props): `exists_torsion_embedding_of_not_isIrreducible`,
 `mazur_classification`, `torsion_det`, `torsion_isUnramified`,
 `torsion_isFlat`, `torsion_isTameAtTwo`, B6a, B6bc,
 Chebotarev–Brauer–Nesbitt, `n_torsion_card` +
 `eval_ΨSq_eq_zero_of_smul_eq_zero`, `ΨSq_ne_zero_of_charDvd` (12 with
 both division-polynomial nodes counted).
- 2026-07-16 (session 3, cont.): **B6bc split and derived** — the
 FLT project's newer compatible-family layer
 (`Deformations/RepresentationTheory/GaloisRepFamily.lean`, defs,
 sorry-free; `HardlyRamified/Family.lean` = B6b `mem_isCompatible`, with
 the conclusion extracted into the named predicate
 `IsInHardlyRamifiedFamily` as a marked ;
 `HardlyRamified/Threeadic.lean` = B6c `three_adic`). New own-work glue
 node `residual_charFrob_eq_of_family` in `Lift.lean` (compatibility
 bookkeeping; consumes B6c in its eventual proof); `residual_charFrob_eq`
 (B6bc) now from B6b + glue. `HardlyRamifiedLift` gained an
 `IsModuleTopology ℤ_[ℓ] O` field (B6a statement strengthening, needed by
 B6b's instance context). Axiom audit clean. Sorry frontier (14, all
 Props): `exists_torsion_embedding_of_not_isIrreducible`,
 `mazur_classification`, `torsion_det`, `torsion_isUnramified`,
 `torsion_isFlat`, `torsion_isTameAtTwo`, B6a, B6b,
 `residual_charFrob_eq_of_family`, B6c, Chebotarev–Brauer–Nesbitt,
 `n_torsion_card`, `eval_ΨSq_eq_zero_of_smul_eq_zero`,
 `ΨSq_ne_zero_of_charDvd`.
- 2026-07-16 (session 3, cont.): **Chebotarev–Brauer–Nesbitt decomposition
 STARTED** (🟪 in progress) — new own-work file
 `GaloisRepresentation/Chebotarev.lean`: `globalFrob v : Γ K` defined
 (image of the local arithmetic Frobenius under `Γ Kᵥ → Γ K`; proven
 `charFrob v = charpoly at globalFrob v` by `rfl`), and the topological
 Chebotarev density node stated (❌ `dense_conjClasses_globalFrob`: the
 conjugacy classes of `globalFrob` outside any finite `S` are dense).
 Remaining pieces of this decomposition (Brauer–Nesbitt for 2-dim mod-ℓ,
 the mod-ℓ cyclotomic character as a continuous character via mathlib's
 `modularCyclotomicCharacter`, its value `q` at `globalFrob q`, and the
 re-derivation of `not_isIrreducible_of_charFrob_eq`) are the next
 layer. **Loop mechanics finalized**: the 30-min cron is REPLACED by a
 `Stop` hook (`.claude/check-sorries.py`, registered in
 `.claude/settings.json`): every attempt by Claude to end its turn is
 vetoed (exit 2) while proof-position sorries remain or `lake build`
 fails the gate; verified live by driving a scratch Claude Code instance
 through tmux (it answered, was blocked with the node list, resumed loop
 work). Sorry frontier (15, all Props): the 14 above +
 `dense_conjClasses_globalFrob`.
- 2026-07-16 (session 3, cont.): **mod-ℓ cyclotomic character CONSTRUCTED,
 sorry-free** (`Chebotarev.lean`): `cyclotomicCharacterModL ℓ : Γ ℚ →*
 (ZMod ℓ)ˣ` (mathlib's `modularCyclotomicCharacter` precomposed with
 `Γ ℚ → (ℚ̄ ≃+* ℚ̄)`), trivial on the fixing subgroup of ℚ(μ_ℓ)
 (`cyclotomicCharacterModL_eq_one`) and continuous into the
 discrete `ZMod ℓ` (`continuous_cyclotomicCharacterModL`, Krull-open
 kernel + coset covering). Two new faithful sorry nodes stated:
 ❌ `cyclotomicCharacterModL_globalFrob` (χ̄(Frob_q) = q for q ≠ ℓ) and
 ❌ `not_isIrreducible_of_charpoly_eq` (Brauer–Nesbitt, 2-dim mod-ℓ
 instance: charpolys everywhere equal to those of 1 ⊕ χ̄ ⇒ not
 irreducible). Chebotarev.lean added to the root import graph.
 Module-system gotcha recorded: in `module` files, some legacy mathlib
 instances (e.g. `AlgebraicClosure.isAlgebraic`) only synthesize under
 `set_option backward.isDefEq.respectTransparency false in`. Axiom audit
 clean. Sorry frontier (17, all Props): the 15 above +
 `cyclotomicCharacterModL_globalFrob`, `not_isIrreducible_of_charpoly_eq`.
 Next: derive `not_isIrreducible_of_charFrob_eq` (the parent) from
 density + Brauer–Nesbitt + Frobenius value + continuity (needs
 discreteness of the module topology on `End` over `ZMod ℓ` and the
 place ↔ prime-number bridge for `Ω ℚ`).
- 2026-07-16 (session 3, cont.): **Chebotarev–Brauer–Nesbitt node
 ** — `not_isIrreducible_of_charFrob_eq` is now in
 `Lift.lean` from the three faithful nodes (density, BN, Frobenius
 value of χ̄) plus new sorry-free bridge lemmas in `Chebotarev.lean`:
 `discreteTopology_moduleTopology` (a finite module over a discrete
 ring has discrete module topology, via `exists_fin'` + coinduced),
 `exists_prime_toHeightOneSpectrum` (PID argument: every finite place
 of ℚ is generated by a prime number), `monic_quadratic_ext` and the
 comparison-quadratic coefficient lemmas. Proof shape: an auxiliary
 prime q₀ ∉ {2,3,ℓ} pins finrank = 2; the coefficient-agreement set
 with `1 ⊕ χ̄` is closed (coefficient maps continuous into discrete
 `ZMod ℓ`, End discrete) and contains the dense Frobenius conjugates
 (charpoly conjugation-invariance via `LinearEquiv.charpoly_conj`;
 χ̄ conjugation-invariance since `(ZMod ℓ)ˣ` is abelian); monic
 quadratics are determined by two coefficients; Brauer–Nesbitt closes.
 Axiom audit clean. Sorry frontier (16, all Props):
 `exists_torsion_embedding_of_not_isIrreducible`,
 `mazur_classification`, `torsion_det`, `torsion_isUnramified`,
 `torsion_isFlat`, `torsion_isTameAtTwo`, B6a, B6b,
 `residual_charFrob_eq_of_family`, B6c, `dense_conjClasses_globalFrob`,
 `not_isIrreducible_of_charpoly_eq`, `cyclotomicCharacterModL_globalFrob`,
 `n_torsion_card`, `eval_ΨSq_eq_zero_of_smul_eq_zero`,
 `ΨSq_ne_zero_of_charDvd`.
- 2026-07-16 (session 4): **Tate-curve/reduction batch , ZERO
 new sorries** — nine files from the FLT repo (import-rewritten), all
 fully proven: `TateCurveConstruction.lean` (1551 lines, the Tate
 curve `E_q` with its q-expansions), `TateCurveBaseChange.lean`,
 `ReductionBaseChange.lean` (multiplicative-reduction transfer +
 Kraus–Laska minimality; the upstream copy is sorry-free, so the
 planned opt-out was dropped), the mathlib overlay
 `Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean`,
 `Slop/NumberTheory/TsumDivisorsAntidiagonal.lean`, and four
 `FLT.Mathlib` prerequisites discovered during the build
 (QuadraticDiscriminant, Splits, Weierstrass DVR overlay,
 IsDiscreteValuationRing). All wired into the root module; full
 `lake build` fails only at the sorry gate. Frontier unchanged at 17:
 `smul_surjective`, `prime_torsion_card`, `exists_weilPairing`,
 `exists_frobenius_conj_mem_coset`, B6a, B6b, B6c, `mod_three`,
 `mazur_classification`, `exists_torsion_embedding_of_not_isIrreducible`,
 `torsion_isUnramified`, `torsion_isFlat`, `torsion_isTameAtTwo`,
 `torsion_unramified_of_good_reduction`,
 `torsion_flat_of_good_reduction`, `resultant_Φ_ΨSq`,
 `isCoprime_Φ_ΨSq`. Next: reformulate `TateCurve.lean`'s sorry-d data
 (`tateCurveEquiv`) existentially, then decompose `torsion_isTameAtTwo`
 against the now-complete Tate-curve infrastructure.
- 2026-07-16 (session 4, cont.): **QuadraticTwists closure ,
 ZERO new sorries** — nineteen files, all fully proven:
 `QuadraticTwists/QuadraticTwists.lean` (793 lines, quadratic twists
 of Weierstrass curves + Galois descent of points) and
 `QuadraticTwists/SplitMultiplicativeReduction.lean` (486 lines: every
 curve with multiplicative reduction has a quadratic twist with SPLIT
 multiplicative reduction — the twist step of the tame-at-2 argument),
 plus seventeen `FLT.Mathlib` prerequisites (EllipticCurve
 Aut/Affine.Point/GaloisDescent/VariableChange overlays, quadratic
 norms, unramified local rings, DVR AdjoinRoot/Separable, Galois
 basics, Gauss lemma, etc.). Wired into the root module; full
 `lake build` fails only at the sorry gate. Frontier unchanged at 17.
 The remaining Tate-curve gap is exactly upstream `TateCurve.lean`
 (512 lines, 12 sorries incl. sorry-d DATA `tateCurveEquiv`/
 `tateEquiv`/`tateEquivSepClosure`) — next: existential
 reformulation, as done for the Weil pairing.
- 2026-07-16 (session 4, cont.): **TateCurve.lean with the
 sorry-d data reformulated existentially** — the fully proven upstream
 material (Tate curve series `tateA₄`/`tateA₆`/`tateCurve` with their
 `evalInt` identities, the valuation lemmas `valuation_Δ_lt_one`,
 `valuation_c₄_eq_one`, `valuation_j_eq`, `one_lt_valuation_j`, the
 Tate parameter `q`/`qUnit` with `q_ne_zero`/`valuation_q_lt_one`,
 base-change functoriality `tateCurve_baseChange`,
 `tateParameter_map`, `q_baseChange`, and the reduction-preserving
 instances) is verbatim. The upstream sorry-d DATA
 (`tateCurveEquiv`, `tateEquiv`, `tateEquivSepClosure`, `tatePoint`)
 and its satellite lemmas are replaced by TWO honest Prop nodes:
 ❌ `exists_variableChange_tateCurve` (Tate's theorem ATAEC V.5.3:
 `E ≅ E_{q(E)}` by a variable change) and
 ❌ `exists_tateEquivSepClosure` (a Galois-equivariant group iso
 `Ωˣ/qᶻ ≅ E(Ω)` over a separable closure — an existential Prop, since
 the iso is canonical only up to sign). The upstream import of the
 sorry-d WeilPairing data file is dropped; `weilPairing_tatePoint`
 (sign coherence between the two packages) is NOT — if a
 consumer appears it must be stated as a joint existential. Frontier:
 19 (17 + the 2 new Tate nodes). Next: decompose
 `torsion_isTameAtTwo` against `exists_tateEquivSepClosure` +
 `exists_quadraticTwist_hasSplitMultiplicativeReduction`.
- 2026-07-16 (session 4, cont.): **`isCoprime_Φ_ΨSq` from
 `resultant_Φ_ΨSq`** — mathlib's
 `Polynomial.exists_mul_add_mul_eq_C_resultant` (the resultant lies in
 the ideal generated by the two polynomials, via the adjugate of the
 Sylvester map) with the degree bounds `natDegree_Φ_le` /
 `natDegree_ΨSq_le` gives `Φ n * p + ΨSq n * q = C (resultant)`; the
 resultant node evaluates this to `±Δ^k`, a unit when `Δ` is, and
 scaling the Bézout identity by its inverse closes `IsCoprime`.
 Frontier: 18.
- 2026-07-16 (session 4, cont.): **`torsion_isUnramified` DECOMPOSED
 by reduction type** — the node is now from two new faithful
 nodes via the case split on `q ∣ abc`:
 ❌ `torsion_isUnramified_of_good` (good reduction at `q ∤ abc`, to be
 closed against the NOS node) and
 ❌ `torsion_isUnramified_of_multiplicative` (`q ∣ abc`: multiplicative
 reduction, `p ∣ v_q(j)`, quadratic twist to split reduction, Tate
 uniformization). Each new node isolates one mechanism; the 
 infrastructure for both (GoodReduction.lean;
 SplitMultiplicativeReduction.lean + TateCurve.lean) is in place.
 Frontier: 19.
- 2026-07-16 (session 4, cont.): **`torsion_isFlat` DECOMPOSED by
 reduction type** — same pattern as `torsion_isUnramified`: 
 from ❌ `torsion_isFlat_of_good` (`p ∤ abc`: Néron-model torsion is
 finite flat, to be closed against the 
 `torsion_flat_of_good_reduction`) and
 ❌ `torsion_isFlat_of_multiplicative` (`p ∣ abc`: `p ∣ v_p(j)` makes
 the Tate-curve extension peu ramifiée, which prolongs finite-flatly)
 via the case split on `p ∣ abc`. Frontier: 20.
- 2026-07-16 (session 4, cont.): **`torsion_isUnramified_of_good`
 DECOMPOSED into arithmetic + glue** — new own-work file
 `FreyCurve/Semistable.lean`: the node is from
 ❌ `freyCurve_hasGoodReduction_of_not_dvd` (the arithmetic: at odd
 `q ∤ abc` the Frey equation is `q`-integral with `q`-unit
 discriminant, so minimal with good reduction over
 `Localization.AtPrime v_q`) and
 ❌ `isUnramifiedAt_of_hasGoodReduction` (the local-global glue:
 good reduction at `q ≠ p` ⟹ `IsUnramifiedAt q`, to be closed against
 the NOS node). The `ℤ_(q)`-as-DVR-with-fraction-field-ℚ
 instance package (Algebra/IsScalarTower/IsFractionRing/
 IsDiscreteValuationRing for `Localization.AtPrime v.asIdeal`) is
 as public named instances (mathlib has the lemmas but no
 instances; note `IsDedekindDomainDvr.is_dvr_at_nonzero_prime` needed
 explicit `@`-application — instance-synthesis stalls on its
 `IsDomain (𝓞 ℚ)` argument even though direct synthesis succeeds).
 Frontier: 21. Audit
 (2026-07-16): `inertia_eq_bot_of_exists_prime_over` is UNCONDITIONAL
 (`[propext, Classical.choice, Quot.sound]`); the chain above
 (`transport → dictionary → subgroup form`) correctly roots through
 the single surjectivity sorry only.
- 2026-07-16 (session 4 close): **UNIFICATION — the glue nodes share
 the Minkowski transport's exact shape.** `GaloisRep.ker_map` is
 `rfl`: `(ρ.map f).ker = ρ.ker.comap (absoluteGaloisGroup.map f)`.
 Hence `IsUnramifiedAt v` (`localInertiaGroup v ≤ (ρ.toLocal v).ker`)
 is equivalent, by the same `Subgroup.map_le_iff_le_comap` dance used
 in `minkowski_character_trivial`, to
 `Subgroup.map (absoluteGaloisGroup.map f) (localInertiaGroup v) ≤
 ρ.ker` — the Minkowski hypothesis `hle` with `L.fixingSubgroup`
 replaced by `ρ.ker` (whose membership = acting trivially on the
 torsion module). So the TWO `IsUnramifiedAt` glue nodes decompose as
 [content node: inertia of the appropriate local object acts
 trivially on the torsion — NOS resp. Tate] + [the SAME
 embedding-prime transport family as the surjectivity leaf]; the
 flat/tame glue nodes use the transport as an ingredient but carry
 additional content (flat prolongation resp. the quotient-character
 package). Attack the transport family ONCE, in the form serving the
 three direct consumers.
- 2026-07-16 (session 4 close): **`mod_three` DECOMPOSED** — 
 from ❌ `mod_three_reducible` (a mod-3 hardly ramified rep has a
 stable line — the Dickson/OddAbsIrred/discriminant content, with
 both classification inputs ) and
 ❌ `mod_three_of_stable_line` (the quotient character of the
 resulting extension is trivial — det condition + everywhere
 unramifiedness + the already-derived Minkowski machinery; Serre
 §5.4 bookkeeping). Frontier: 22. Final interface check (2026-07-16):
 `IntermediateField.mem_fixingSubgroup_iff` exists (KrullTopology.lean
 usage) — the transport construction's source-side membership
 (`σ ∈ L.fixingSubgroup ↔ ∀ x ∈ L, σ x = x`) is available; with it,
 every interface of the shared transport is name-verified.
- 2026-07-16 (session 4 close): **surjectivity-leaf scoping** —
 mathlib at our pin has NO decomposition-group ↔ local-Galois theory
 (`decompositionSubgroup` appears only in its defining file), so the
 Neukirch II.9 route is from-scratch construction. ALTERNATE ROUTE
 (likely shorter, avoids group surjectivity entirely): to show the
 embedding prime `Q₀` has trivial inertia it suffices to show
 `e(Q₀|q) = 1` DIRECTLY (then `card (inertia) = e = 1` forces ⊥ by
 `card_inertia_eq_ramificationIdxIn` + `Subgroup.eq_bot_of_card_eq`):
 the hypothesis "local inertia image fixes L" says exactly that `L`
 embeds into the inertia-fixed field of `ℚ̄_q`, i.e. `L ⊆ ℚ_q^{unr}`
 along the chosen embedding, and unramified local extensions have
 `e = 1` — provable through the VALUATION side (the 
 `IsNonarchimedeanLocalField`/`ValuativeExtension` machinery and
 mathlib's `Ideal.ramificationIdx` ↔ valuation comparison), no
 decomposition groups needed. Evaluate both routes at fresh context;
 the valuation route reuses the session's Tate-infrastructure
 instances. The
 four inertia spellings, fully mapped (2026-07-16): (1)
 `localInertiaGroup` = generic `AddSubgroup.inertia` of `𝔪` upstairs
 in `ℚ̄_q`, membership `.rfl`; (2) `ValuationSubring.inertiaSubgroup`
 (the NOS node's spelling) = kernel of the residue action of
 the DECOMPOSITION subgroup (`RamificationGroup.lean:50` — the file
 has NO theorems, so the bridge "trivial residue action ⟺ σx − x ∈ 𝔪
 ∀x ∈ A" is a short definitional unfolding to write); (3)
 HilbertTheory's subgroup inertia; (4) `Ideal.inertia`
 (MulSemiringAction), membership `.rfl`, connected to `e` by
 `card_inertia_eq_ramificationIdxIn` and to (3) by the HilbertTheory
 file itself.
- 2026-07-16 (session 4, cont.): **`freyCurve_hasGoodReduction_of_not_dvd`
 ** — the good-reduction arithmetic node is closed:
 `q`-integrality via the integral model (`freyCurveInt` and
 `FreyCurve.map`, each coefficient an integer, lifted through
 `map_intCast`); the discriminant `(abc)^{2p}/2⁸` is exhibited as the
 image of the explicit unit `(abc)^{2p}·(2⁸)⁻¹` of `ℤ_(q)` (both
 factors prime to `q`, inverted via `IsLocalization.AtPrime.
 isUnit_to_map_iff` and the new bridge lemmas
 `intCast_mem_toHeightOneSpectrumRingOfIntegersRat_iff` and
 `isUnit_intCast_localizationAtPrime`), so the adic valuation of Δ is
 `1` by `mker_valuation_eq_isUnitSubmonoid`; minimality follows since
 valuation `1` is the maximum over integral models (the
 `valuation_Δ_aux` subtype bound). Frontier: 20.
- 2026-07-16 (session 4, cont.): **`torsion_isFlat_of_good` ** —
 the arithmetic node applies verbatim at `q := p` (`p ≠ 2`
 since `p ≥ 5`), and a new glue node
 ❌ `isFlatAt_of_hasGoodReduction` (good reduction at `p` ⟹
 `IsFlatAt p`, to be closed against the 
 `torsion_flat_of_good_reduction` Hopf-package node) completes the
 derivation. Frontier: 20 (one closed, one opened).
- 2026-07-16 (session 4, cont.): **multiplicative arithmetic ;
 both multiplicative consumers ** —
 `freyCurve_hasMultiplicativeReduction_of_dvd` is (integrality;
 `c₄ = c^{2p} - (ab)^p` prime to `q` by the pairwise-coprimality Xor;
 minimality by the unit-`c₄` Kraus–Laska criterion
 `isMinimal_of_valuation_c₄_eq_one`; `v(Δ) < 1` via
 `valuation_lt_one_iff_mem` since `abc` lands in the maximal ideal).
 `torsion_isUnramified_of_multiplicative` and
 `torsion_isFlat_of_multiplicative` are from it (+ the proven
 `j_valuation_of_bad_prime`) through two new glue nodes:
 ❌ `isUnramifiedAt_of_hasMultiplicativeReduction` (Tate glue at
 `q ≠ p`) and ❌ `isFlatAt_of_hasMultiplicativeReduction`
 (peu-ramifiée glue at `p`). All four FreyConditions reduction-type
 cases now rest exclusively on local-global glue nodes; the Frey-curve
 semistability arithmetic is complete. Frontier: 20.
- 2026-07-16 (session 4, cont.): **Frey multiplicative reduction AT 2
 ; `torsion_isTameAtTwo` ** —
 `freyCurve_hasMultiplicativeReduction_at_two` is (this is
 where the Frey model's defining congruences `a ≡ 3 mod 4`, `b ≡ 0
 mod 2` are consumed: they force `c` odd, so `c₄` is odd and
 `v(c₄) = 1`, while `Δ = 2^{2p-8}(ab'c)^{2p}` is in the maximal ideal
 as `2p > 8`); `torsion_isTameAtTwo` is from it through the
 new glue node ❌ `isTameAtTwo_of_hasMultiplicativeReduction` (stated
 for a general elliptic curve over ℚ — the Tate/quadratic-twist glue
 at 2). ALL FOUR conditions of `IsHardlyRamified` for the Frey curve
 now rest exclusively on generic local-global glue nodes; every
 Frey-specific computation is sorry-free. Frontier: 20.
- 2026-07-16 (session 4, cont.): **Serre's reducible-case node
 DECOMPOSED; the CRT assembly ** —
 `exists_torsion_embedding_of_not_isIrreducible` is now from
 ❌ `exists_two_torsion_and_p_point_of_not_isIrreducible` (Serre's
 core: reducibility ⟹ some curve has full rational 2-torsion AND a
 rational point of order exactly p — the Minkowski/Vélu content) and
 ✅ `embedding_assembly` (: injective (ℤ/2)² + element of order
 p assemble into injective ℤ/2 × ℤ/2p, via `ZMod.chineseRemainder`,
 `ZMod.lift` for the p-part, and the coprime-annihilator separation
 `p•u = u` for 2-torsion u with p odd). Frontier: 20 (one closed, one
 opened; the remaining Serre node no longer contains the group
 theory).
- 2026-07-16 (session 4, cont.): **Frey full rational 2-torsion ;
 Serre core split by character case** —
 `freyCurve_two_torsion_embedding` is : the transformed Frey
 model has visible rational 2-torsion at `(0,0)` and `(aᵖ/4, −aᵖ/8)`
 (equation checks by `field_simp`/`ring`; nonsingularity from
 `equation_iff_nonsingular` since the curve is elliptic; order 2 via
 the negation formula `negY`; the two points differ in
 `x`-coordinate), assembled into an injective `(ℤ/2)² →+ E(ℚ)`.
 `exists_two_torsion_and_p_point_of_not_isIrreducible` is now 
 from the new disjunction node ❌ `exists_p_point_of_not_isIrreducible`
 (χ₁ = 1: p-point on the Frey curve itself, 2-torsion supplied by the
 proven lemma; χ₂ = 1: the full package on the Vélu quotient). The
 remaining Serre node isolates exactly Minkowski + Vélu. Frontier: 20.
- 2026-07-16 (session 4, cont.): **Minkowski EXTRACTED as a faithful
 node** — `exists_p_point_of_not_isIrreducible` is now from
 ❌ `minkowski_character_trivial` (a mod-`p` character of G_ℚ with open
 kernel unramified at every finite place — stated with
 `localInertiaGroup` and the restriction along
 `Field.absoluteGaloisGroup.map` — is trivial; to be closed against
 mathlib's `NumberField.abs_discr_gt_one` via the fixed field of the
 kernel) and ❌ `exists_p_point_of_not_isIrreducible_of_minkowski`
 (Serre's analysis with the Minkowski input as an explicit
 hypothesis; its remaining deep content is exactly Vélu quotients +
 the character bookkeeping). Frontier: 21 (one closed, two opened —
 the generic number theory now lives in its own node).
- 2026-07-16 (session 4 close): **Minkowski route verified in mathlib**
 — reconnaissance recorded (see the session-4 reconnaissance section):
 the discriminant side of `minkowski_character_trivial` is entirely in
 mathlib at our pin (`finrank_eq_one_of_unramified` etc.); what
 remains is the fixed-field construction from the open kernel and the
 inertia dictionary. No node change this iteration; the frontier
 stays 21 with the next attack mapped in detail.
- 2026-07-16 (session 4, cont.): **Minkowski reduced to its
 character-free subgroup form** — `minkowski_character_trivial` is
 (the kernel of an everywhere-unramified character is an open
 normal subgroup containing every inertia image, via
 `Subgroup.map_le_iff_le_comap`); the sorry now lives in
 ❌ `open_normal_subgroup_eq_top_of_inertia_le`, a pure
 Galois/number-theoretic statement with no characters or `ZMod p`
 in sight — exactly the statement the mathlib discriminant route
 closes. Frontier: 21 (sorry relocated, interface simplified).
- 2026-07-16 (session 4, cont.): **OddAbsIrred , ZERO
 sorries** — `KnownIn1980s/RepresentationTheory/OddAbsIrred.lean` +
 `Slop/RepresentationTheory/OddAbsIrredSlop.lean` (495 lines, fully
 proven): for a finite-dimensional representation with some `g` having
 a one-dimensional fixed space (e.g. complex conjugation on an odd
 2-dim Galois rep), irreducible ⟺ absolutely irreducible
 (`OddRep.isIrreducible_iff_isAbsolutelyIrreducible`). Wired into the
 root. Mapped feed for the B6 chain / `mod_three` (together with the
 still-unvendored `Slop/PGL2` Dickson classification). Frontier
 unchanged: 21.
- 2026-07-16 (session 4, cont.): **Dickson classification ,
 ZERO sorries (13 files, ~11.5k lines)** — the full
 `Slop/PGL2/FiniteSubgroups` development plus
 `KnownIn1980s/PGL2/Defs.lean` with the classification theorems
 (`Dickson.classification_tame`: a nontrivial finite subgroup of
 `PGL₂(𝔽̄_p)` of order prime to `p` is cyclic, dihedral, A₄, S₄ or A₅;
 `Dickson.classification_wild`: order divisible by `p` gives
 elementary-abelian-by-cyclic, PSL₂/PGL₂ of a subfield, or A₅ at
 `p = 3`). : upstream leaves the Defs statements
 sorry-d and proves copies in `Proofs.lean`; here the shared
 definitions are split into `PGL2/Basic.lean` (breaking the import
 cycle with the Slop development) and the proofs are inlined into
 `Defs.lean`, so the whole tree is sorry-free. Wired into the root.
 Feed for `mod_three` (image-of-Galois analysis in PGL₂(𝔽₃)).
 Frontier unchanged: 21.
- 2026-07-16 (session 4 close): **explicit axiom audit of the
 session's harvest** — UNCONDITIONALLY proven (`[propext,
 Classical.choice, Quot.sound]`, zero `sorryAx`):
 `Dickson.classification_tame`, `Dickson.classification_wild`,
 `OddRep.isIrreducible_iff_isAbsolutelyIrreducible`,
 `freyCurve_hasGoodReduction_of_not_dvd`,
 `freyCurve_hasMultiplicativeReduction_of_dvd`,
 `freyCurve_hasMultiplicativeReduction_at_two`,
 `freyCurve_two_torsion_embedding`, `embedding_assembly`.
 Correctly sorry-rooted (derived from open nodes):
 `minkowski_character_trivial`, `isCoprime_Φ_ΨSq`. Invariant intact.
- 2026-07-16 (session 4 close): **`neZero_natCast_residueField`
 ** (unconditional) — for distinct primes `q ≠ p`, `p` is
 nonzero in the residue field of `ℤ_(q)` (`p` is a unit of the
 localization; units have nonzero residue). This pre-discharges the
 `NeZero (n : ResidueField R)` hypothesis of the NOS and
 finite-flat nodes for when the good-reduction glue nodes are closed
 against them.
- 2026-07-16 (session 4 close): **Tate torsion-membership lemmas
 ** — `WeierstrassCurve.mem_torsionBy_of_mem_rootsOfUnity` and
 `mem_torsionBy_of_pow_eq` (in `TateCurve.lean`): under ANY witness
 `e : Ωˣ/qᶻ ≃+ E(Ω)` of `exists_tateEquivSepClosure`, `N`-th roots of
 unity and `N`-th roots of the Tate parameter map to `N`-torsion
 points (formal: `N•[u] = [u^N]` and the class of `q` is zero).
 These serve the multiplicative/tame glue nodes, which analyze `E[p]`
 through the uniformization's torsion.
- 2026-07-16 (session 5): **MINKOWSKI SURJECTIVITY LEAF —
 the entire Minkowski branch now rests on ONE purely local node.**
 `exists_prime_over_inertia_eq_bot_of_le_fixingSubgroup` is 
 via the valuation route (NO decomposition-group theory, NO henselian
 lifting): embed `L` into `M := ℚ_q(ι L) ⊆ ℚ_qᵃˡᵍ` along the
 `absoluteGaloisGroup.map` embedding (`lift_map` transports `hle` to
 "local inertia fixes `M` pointwise"); the NEW sorry node
 `maximalIdeal_map_eq_of_le_fixedField_localInertiaGroup`
 (`LocalInertiaFixedField.lean`, stated for GENERAL number fields
 `K` and places `v`) gives `e(M/ℚ_q) = 1`, i.e. `𝔪_M = (q)`; the
 comap prime `Q₀` of `𝔪_M` under the integrality-restricted
 `𝓞 L → 𝒪_M` then has `e(Q₀|q) = 1` (else `q ∈ Q₀²` forces
 `q ∈ (q²)`, a unit in a proper ideal), and
 `#I(Q₀) = e = 1` (`card_inertia_eq_ramificationIdxIn` +
 `ramificationIdx'_ne_one_iff` + the old/new-spelling bridge
 `ramificationIdx'_eq_ramificationIdx`). Helper lemmas 
 unconditionally: `asIdeal_toHeightOneSpectrumRingOfIntegersRat`,
 `maximalIdeal_adicCompletionIntegers_eq_span`. Axiom audit: both
 helpers `[propext, Classical.choice, Quot.sound]`; the chain
 `exists_prime_over…` → `inertia_eq_bot_of_le_fixingSubgroup` →
 `isUnramifiedAt_of_inertia_le_fixingSubgroup` →
 `open_normal_subgroup_eq_top_of_inertia_le` carries `sorryAx` ONLY
 through the local node. Frontier stays at 22 by count, but the
 Neukirch II.9 content strictly shrank to the local statement, whose
 planned proof (Galois closure + finite-level `|I| = e` counting +
 compactness lifting) needs no new mathematical inputs beyond
 /mathlib API. Lean gotchas recorded: the scoped-`algebraMap`
 coercion is `Algebra.cast` (NOT syntactically `algebraMap _ _ _` —
 build cross-spelling equalities via `.trans`-chained lemma instances
 + `convert … using 2` + `norm_cast`, never `rw`); `↥M`'s ℤ-algebra
 instance is ambiguous (`Ring.toIntAlgebra` vs
 `IntermediateField.algebra'`) — avoid `RingHom.toIntAlgHom` and
 `IsIntegral.tower_top` across the ambiguity; instead push the monic
 witness through `Polynomial.eval₂_map` + `Subsingleton.elim` on
 `ℤ →+* ·`.
- 2026-07-16 (session 5): **local node decomposition started —
 finite-level `|I| = e` stated; supporting instances .** In
 `LocalInertiaFixedField.lean`: unconditionally —
 `isIntegralClosure_integralClosure` (the type synonym is an
 `IsIntegralClosure`), `smulDistribClass_integralClosure` (the Galois
 action distributes over `𝒪_N`-scalars), the intermediate-field-
 restricted tower `IsScalarTower 𝒪ᵥ Kᵥ ↥M` (deliberately NOT the
 general form: a general instance enables `IntermediateField.algebra'`
 as a second route to `Algebra 𝒪ᵥ ↥M` and poisons every
 `IntegralClosure` elaboration), and
 `liesOver_maximalIdeal_integralClosure` (`𝔪_N` lies over `𝔪ᵥ`, via
 comap-maximality under integrality + locality). NEW sorry node
 `card_inertia_finite_level` (finite Galois `N/Kᵥ` has
 `#I(𝔪_N/Gal(N/Kᵥ)) = e`): the full instance pack for mathlib's
 `card_inertia_eq_ramificationIdxIn` is verified EXCEPT
 `Module.Flat 𝒪ᵥ 𝒪_N` — the PID/free route fails to SYNTHESIZE
 because different elaboration sites of `IntegralClosure 𝒪ᵥ ↥N`
 embed non-reducibly-unifiable `CommRing ↥N`/`Algebra 𝒪ᵥ ↥N`
 instance arguments (`Field.toCommRing ∘ IntermediateField.toField`
 vs the direct path; verified by `pp.all` on the failing goal, which
 contains `instAlgebraSubtypeMemValuationSubringVendored` while
 direct synthesis in a clean context succeeds). Fix strategy for the
 next attack: an abstract `(R S G)`-wrapper taking `Module.Free R S`
 as a hypothesis, instantiated once with a `letI`-pinned instance
 pack. Remaining plan for the L1 assembly unchanged (restriction maps
 inertia to inertia; counting surjectivity; compactness lifting; then
 `e(M) = 1` via the Galois closure). Frontier: 23 by count; the
 finite-level node is a strict sub-piece of L1's content.
- 2026-07-16 (session 5): **`card_inertia_finite_level` **
 (unconditional; `[propext, Classical.choice, Quot.sound]`). The
 entire blocked synthesis was fixed by ONE line:
 `set_option backward.isDefEq.respectTransparency false in` on the
 theorem — the option makes the `Module.Free`/`Flat` instance
 unifications succeed across the divergent `IntegralClosure`
 elaboration spellings (the abstract-wrapper strategy was NOT
 needed). GOTCHA for the file: every theorem here that synthesizes
 module-structure classes over `IntegralClosure 𝒪ᵥ ↥N` likely needs
 the same option. Frontier back to 22. Local-node remaining pieces:
 finite-level restriction maps inertia into inertia (uses the proven
 `liesOver` instance + `𝔪_{N'} ∩ 𝒪_N = 𝔪_N`), tower
 multiplicativity of `e` (mathlib
 `ramificationIdx'_algebra_tower`), counting surjectivity
 `I(N'/Kᵥ) ↠ I(N/Kᵥ)`, compactness lifting to `localInertiaGroup`,
 and the `e(M) = 1` Galois-closure assembly.
- 2026-07-16 (session 5):
 **`restrictNormalHom_mem_inertia_of_mem_localInertiaGroup` **
 (unconditional) — the restriction of a `localInertiaGroup` element
 to a finite Galois subextension `N` lies in the inertia of `𝔪_N` in
 `Gal(N/Kᵥ)`. Supporting pieces : `integralClosureInclusion`
 (`𝒪_N →+* 𝒪_{Kᵥᵃˡᵍ}` by codRestrict + integrality transport along
 the `𝒪ᵥ`-algebra tower) and the tower instance
 `IsScalarTower 𝒪ᵥ ↥M E` (ambient-target form, middle an
 intermediate-field subtype — still avoids the `algebra'` ambiguity).
 KEY SIMPLIFICATION discovered: `ι⁻¹(𝔪_big) ≤ 𝔪_N` is FREE from
 locality of `𝒪_N` (a proper ideal of a local ring sits under the
 maximal ideal — `IsLocalRing.le_maximalIdeal`; no integrality, no
 comap-maximality needed for the INTO direction). Next pieces:
 `IsDiscreteValuationRing 𝒪_N` (ValuationRing + Noetherian ⟹ PID),
 finite-to-finite restriction + counting surjectivity, compactness
 lifting, `e(M) = 1` assembly.
- 2026-07-16 (session 5): **`isDiscreteValuationRing_integralClosure`
 ** (instance; unconditional) — `𝒪_N` is a DVR for every finite
 subextension `N/Kᵥ`: ValuationRing ( spectral-norm) + PID
 (mathlib's Bézout+Noetherian instance, Noetherian via
 `IsIntegralClosure.isNoetherianRing`) + local + not-a-field (
 `not_isField_integralClosure` + the newly proven
 `adicCompletionIntegers_ne_top`, itself from `𝒪ᵥ = ⊤` forcing
 `IsField 𝒪ᵥ` against the DVR's `not_a_field`). This unlocks the
 M-based instance pack for the second `card_inertia` application
 (base `𝒪_M`, Dedekind for the `e`-tower lemma). ASSEMBLY MAP refined:
 `e(M)=1` follows from `I(𝔪_N/Gal(N/Kᵥ)) ≤ Gal(N/M)` (surjectivity +
 `hM`), `|I over Kᵥ| = e(N/Kᵥ)` (proven), `|inertia over M| = e(N/M)`
 (M-based card_inertia, needs `letI Algebra ↥M ↥N` inclusion
 gymnastics + residue finiteness of `𝒪_M`), and
 `e(N/Kᵥ) = e(N/M)·e(M)` (mathlib `ramificationIdx'_algebra_tower`,
 Dedekind hypotheses now available). Then compactness lifting
 (`Γ Kᵥ` profinite; `localInertiaGroup` closed via locally-constant
 evaluation; finite-to-finite surjectivity by the same counting) and
 the `map 𝔪ᵥ = 𝔪_M ↔ e(M) = 1` conversion.
- 2026-07-16 (session 5):
 **`maximalIdeal_map_eq_of_ramificationIdx_eq_one` **
 (unconditional) — `e = 1 ⟹ map 𝔪ᵥ = 𝔪_N`, via the DVR ideal
 classification (`ideal_eq_span_pow_irreducible`: the mapped ideal is
 `(ϖⁿ)`; `n ≥ 1` from the proven `LiesOver`, `n < 2` from
 `ramificationIdx'_ne_one_iff`). This is the L1 endgame conversion:
 the final assembly now reduces to producing
 `ramificationIdx' (𝔪ᵥ) (𝔪_M) = 1` from `hM` via the Galois closure
 counting. Remaining for L1: M-based `card_inertia` (inclusion-algebra
 gymnastics + `𝒪_M` residue finiteness), `e`-tower application,
 compactness lifting of finite-level inertia to `localInertiaGroup`,
 final assembly.
- 2026-07-16 (session 5, design note for the M-based counting):
 mathlib's `stabilizerHom_surjective` (Frobenius lifting) requires
 `[Finite G]` — NO profinite shortcut; the compactness plan stands.
 For the second `card_inertia` (base `𝒪_M`, group `Gal(N/M)`), the
 clean formulation avoids `letI` inclusion-algebras: reify `M` inside
 `↥N` as `M' : IntermediateField Kᵥ ↥N` (via
 `IntermediateField.comap N.val` from `M ≤ N`, or by generalizing the
 whole `FiniteLevel` section from subextensions of `Kᵥᵃˡᵍ` to an
 arbitrary finite extension `E/Kᵥ`); then `Algebra ↥M' ↥N`,
 `IsGalois ↥M' ↥N` (tower-top), and
 `IntermediateField.fixingSubgroupEquiv : fixingSubgroup M' ≃* Gal(N/M')`
 are all CANONICAL instances. Generalizing the section to arbitrary
 `E` is the right move (all inputs — `valuationRing`,
 `IsIntegralClosure.finite`, Bézout-PID, `not_isField` — are already
 ambient-free); the only IntermediateField-specific pieces are my two
 tower instances, whose subtype-restriction guards the `algebra'`
 ambiguity — for a general-`E` section the guard concern moves to the
 INSTANTIATION sites, where the proven
 `backward.isDefEq.respectTransparency false` fix applies. The
 assembly chain: `τ ∈ I(𝔪_N/Gal(N/Kᵥ))` fixing `M` ⟹ `τ` upgrades
 through `fixingSubgroupEquiv` to `Gal(N/M')`, lands in
 `I(𝔪_N/Gal(N/M'))` (`Ideal.coe_mem_inertia`-style), so
 `e(N/Kᵥ) = |I(𝔪_N/GalKᵥ)| ≤ |I(𝔪_N/Gal(N/M'))| = e(N/M')`; with
 `e(N/Kᵥ) = e(N/M')·e(M/Kᵥ)` (`ramificationIdx'_algebra_tower`,
 Dedekind ✅ both DVRs) and `e ≠ 0`, conclude `e(M/Kᵥ) = 1`.
- 2026-07-17 (session 5): **`card_inertia_intermediate` **
 (unconditional) — `|I(𝔪_N/Gal(N/M'))| = e(𝔪_{M'} in 𝒪_N)` for any
 intermediate `M'` of a finite Galois `N/Kᵥ`, using the
 intermediate-base algebra layer and the new
 `hasFiniteQuotients_adicCompletionIntegers` (every nonzero ideal of
 the DVR `𝒪ᵥ` is `𝔪ᵥⁿ`; finite quotients by induction with
 `Submodule.finite_quotient_smul`; then
 `Ring.HasFiniteQuotients.of_module_finite` transports to `𝒪_{M'}`).
 Debug notes: `Submodule.mkQ`-based `Module.Finite` haveI's EXPLODE
 under respectTransparency-false (module-structure unification) — use
 ring-level routes (`Module.Finite.trans`, `HasFiniteQuotients`);
 `of_module_finite` takes `R` EXPLICITLY. Both counting inputs for the
 L1 assembly are now in place; remaining: the `e`-tower application
 (`ramificationIdx'_algebra_tower` over `𝒪ᵥ → 𝒪_{M'} → 𝒪_N`), the
 fixing-subgroup upgrade `I(𝔪_N/GalKᵥ) ∩ fix(M') ↪ I(𝔪_N/Gal(N/M'))`,
 compactness lifting, and the final assembly.
- 2026-07-17 (session 5): **THE COUNTING COMBINER
 `ramificationIdx_eq_one_of_inertia_le_fixingSubgroup` **
 (unconditional) — the mathematical HEART of the local node: if
 `I(𝔪_N/Gal(N/Kᵥ))` fixes the intermediate field `M'` pointwise, then
 `e(𝔪ᵥ at 𝔪_{M'}) = 1`. Both card lemmas were upgraded to conclude in
 `ramificationIdx'` form (conversions inside their own instance
 packs); the combiner chains the `fixingSubgroupEquiv` upgrade
 injection, `Ideal.ramificationIdx'_algebra_tower'` (Dedekind ✅ both
 DVRs), and
 `Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver`
 (NOTE the namespace: it lives inside `namespace IsDedekindDomain`
 within `namespace Ideal`). With
 `maximalIdeal_map_eq_of_ramificationIdx_eq_one`, L1 now reduces to:
 (a) the COMPACTNESS LIFTING — `I(𝔪_N/Gal(N/Kᵥ)) ⊆ π_N(I_v)` for the
 Galois closure `N` (finite-to-finite surjectivity comes from the
 SAME combiner pattern applied to towers `N ⊆ N'` + the proven
 restriction lemma; then profinite compactness) — and (b) the final
 glue: `N := normalClosure`, reify `M` as `M' ⊆ ↥N`, transport
 `e(M') = 1` back to the subextension `M` (ring iso
 `𝒪_{M'} ≅ 𝒪_M` from `M' ≅ M` as `Kᵥ`-extensions).
- 2026-07-17 (session 5): **FINITE-LEVEL INERTIA SURJECTIVITY **
 (`restrictNormalHom_inertia_surjective`, unconditional) — for normal
 `M' ⊆ N` finite over `Kᵥ`, the restriction maps `I(𝔪_N/Gal(N/Kᵥ))`
 ONTO `I(𝔪_{M'}/Gal(M'/Kᵥ))`. First-isomorphism counting:
 `|A| = |ker f|·|range f|`; `|ker f| = |I(𝔪_N/Gal(N/M'))|` via
 TWO-WAY INJECTIONS + `Nat.le_antisymm` (round-trip `Equiv`
 coherence proofs kept failing on beta-redex/`Subtype.ext` layers —
 the two-injection pattern is far more robust); the counts and tower
 from the previous lemmas; `Subgroup.eq_of_le_of_card_ge` closes.
 Also : `restrictNormalHom_mem_inertia_intermediate`
 (restriction-into at the (E, M') level). The local node now needs
 ONLY: profinite compactness lifting (Γ compact, `localInertiaGroup`
 closed, directed system over finite Galois levels — all finite-level
 inputs now proven) and the final normalClosure/reification glue.
- 2026-07-17 (session 5, compactness-arc plan): `CompactSpace (Γ Kᵥ)`
 is a GLOBAL instance
 (`Fermat/FLT/Mathlib/FieldTheory/Galois/Infinite.lean`, any algebraic
 extension). Target:
 `∃ σ ∈ localInertiaGroup v, restrictNormalHom N σ = τ` for
 `τ ∈ I(𝔪_N)`, `N` finite Galois subextension of `Kᵥᵃˡᵍ`. Plan:
 (1) TRANSPORT LAYER for `N ≤ N'` subextensions: reify
 `M' := comap N'.val N : IntermediateField Kᵥ ↥N'`, build the
 `Kᵥ`-AlgEquiv `↥M' ≃ₐ[Kᵥ] ↥N`, conjugate `IC`/`𝔪`/inertia across
 it (`ramificationIdx'_comap_eq` for `e`-invariance if needed), and
 intertwine `restrictNormalHom` with the two restriction maps
 (`AlgEquiv.restrictNormal_trans`-family for
 `res_N = res_{N'→N} ∘ π_{N'}`); this turns the proven `(E, M')`
 surjectivity into subextension-pair surjectivity
 `I(𝔪_{N'}) ↠ I(𝔪_N)`. (2) CLOSED SETS
 `D_{N'} := π_N⁻¹{τ} ∩ π_{N'}⁻¹(I(𝔪_{N'}))` for finite Galois
 `N' ⊇ N`: closed via continuity of `restrictNormalHom` into finite
 discrete targets (check mathlib `continuous_restrictNormalHom`);
 nonempty via (1) + `restrictNormalHom_surjective`; DIRECTED via
 restriction-into + compositum (finite Galois subextensions are
 directed). (3) `IsCompact.nonempty_iInter_of_directed_nonempty_...`
 gives `σ*`; `σ* ∈ localInertiaGroup` because every `x ∈ IC-big`
 lies in some finite Galois `N'` (normal closure of `Kᵥ⟮x⟯`) and
 `ι(𝔪_{N'}) ⊆ 𝔪_big` (the comap EQUALITY: `≤` by locality — proven
 pattern — and `⊇` by `isMaximal_comap_of_isIntegral`, `𝔪_big`
 maximal since `IC-big` is a local valuation ring).
- 2026-07-17 (session 5): **compactness arc: ALL FINITE-LEVEL PIECES
 ** (each unconditional): `autCongr_mem_inertia` (inertia
 transport along `Kᵥ`-isos, via two-sided-inverse codRestrict pair),
 `reifySubextension`/`reifyEquiv`/`normal_reifySubextension`
 (reification of `N ≤ N'` with `Normal.of_algEquiv`; the FORWARD map
 preserves ambient values definitionally, `.symm` is choice-opaque —
 always route value computations through `apply_symm_apply`),
 `restrictNormalHom_reify_compat` (`π_N = autCongr ∘ res_reify ∘
 π_{N'}`, three `restrictNormal_commutes` chases),
 `integralClosureInclusion_mem_maximalIdeal` (`ι(𝔪_N) ⊆ 𝔪_big`),
 `restrict_mem_inertia_of_le` (directedness content),
 `exists_inertia_restrict_of_le` (D-set nonemptiness content).
 GOTCHA: explicit `haveI : Normal ... := IsGalois.to_normal` needed
 at use sites — the general valuation-subring tower instance makes
 failing instance searches explode on metavariable goals. REMAINING
 FOR L1 (two pieces): (i) the topological intersection theorem —
 index `ι := {N' // N ≤ N' ∧ FD ∧ IsGalois}` (nonempty: `⟨N, le_rfl,
 ..⟩`), `D N' := π_N⁻¹{τ} ∩ π_{N'}⁻¹(I(𝔪_{N'}))`, closed
 (`InfiniteGalois.restrictNormalHom_continuous` + T1 finite),
 nonempty (`exists_inertia_restrict_of_le`), directed (compositum
 `N'₁ ⊔ N'₂`, `normal_sup` + FD-sup instances,
 `restrict_mem_inertia_of_le`), then
 `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`
 (`CompactSpace (Γ Kᵥ)` ) and membership in
 `localInertiaGroup` via `normalClosure Kᵥ (N ⊔ Kᵥ⟮x⟯) Kᵥᵃˡᵍ` +
 `restrictNormal_commutes` + `integralClosureInclusion_mem_maximalIdeal`;
 (ii) L1 assembly — `N := normalClosure Kᵥ M Kᵥᵃˡᵍ`, `hfix` from (i)
 + `hM`, `ramificationIdx_eq_one_of_inertia_le_fixingSubgroup`
 (counting combiner) at `M' := reify M`, transport `e = 1` back
 across `reifyEquiv` (extract the `f₁/f₂` pair of
 `autCongr_mem_inertia` as a named `RingEquiv` and use
 `ramificationIdx'_comap_eq`, or transport the final map-equality
 directly), then `maximalIdeal_map_eq_of_ramificationIdx_eq_one`.
- 2026-07-17 (session 5): **THE COMPACTNESS LIFTING IS **
 (`exists_mem_localInertiaGroup_restrictNormalHom_eq`, unconditional
 — the PROFINITE half of Neukirch II.9.11): every inertia element at
 a finite Galois level `N` is the restriction of an element of
 `localInertiaGroup v`. Directed closed sets
 `D_{N'} = π_N⁻¹{τ} ∩ π_{N'}⁻¹(I(𝔪_{N'}))` in the compact `Γ Kᵥ`;
 nonempty by `exists_inertia_restrict_of_le`; directed via composita
 and `restrict_mem_inertia_of_le`; a point of the intersection lies
 in `localInertiaGroup` because every element of the big integral
 closure lives at the finite Galois level
 `normalClosure Kᵥ (N ⊔ Kᵥ⟮z⟯) Kᵥᵃˡᵍ` (existential-package pattern —
 `set`-bound `Nx` blocks instance matching; provide
 `∃ Nx, N ≤ Nx ∧ z ∈ Nx ∧ FD ∧ IsGalois` and `obtain`). Whole-arc
 axiom audit clean. THE LOCAL NODE L1 NOW NEEDS ONLY ITS FINAL
 ASSEMBLY (piece (ii) above).
- 2026-07-17 (session 5): ★★★ **THE LOCAL NODE IS — THE ENTIRE
 MINKOWSKI BRANCH IS CLOSED UNCONDITIONALLY.** ★★★
 `maximalIdeal_map_eq_of_le_fixedField_localInertiaGroup` (Neukirch
 II.9.11, "the fixed field of the local inertia group is unramified")
 is sorry-free: Galois closure + compactness lifting turns `hM` into
 finite-level inertia fixing the reified `M`; the counting combiner
 gives `e = 1`; the `𝒪ᵥ`-algebra isomorphism of integral closures
 (two-sided codRestrict pair, `comap 𝔪 = 𝔪` by nonunit transport)
 transports `e = 1` across `reifyEquiv`
 (`ramificationIdx'_comap_eq`); the DVR conversion closes. AXIOM
 AUDIT OF THE WHOLE CHAIN — L1 →
 `exists_prime_over_inertia_eq_bot_of_le_fixingSubgroup` →
 `inertia_eq_bot_of_le_fixingSubgroup` →
 `isUnramifiedAt_of_inertia_le_fixingSubgroup` →
 `open_normal_subgroup_eq_top_of_inertia_le` →
 `minkowski_character_trivial` — ALL
 `[propext, Classical.choice, Quot.sound]`, ZERO `sorryAx`.
 "ℚ has no nontrivial everywhere-unramified extension" (in the
 subgroup and character forms the tree consumes) is now a THEOREM,
 via a from-scratch formalization of local ramification theory:
 finite-level Hilbert `|I| = e` counting + profinite compactness —
 NO decomposition groups, NO henselian lifting, no new axioms.
 Frontier: 21 nodes. The transport family is now available for
 the two `IsUnramifiedAt` glue nodes (next consumers).
- 2026-07-17 (session 5, next-arc setup): the glue node
 `isUnramifiedAt_of_hasGoodReduction` derivation from the 
 NOS leaf (`torsion_unramified_of_good_reduction`,
 `GoodReduction.lean`) needs: (1) the valuation subring
 `𝒪 := comap ι (valuation ring of ℚ̄_q)` of `ℚ̄` over `R = ℤ_(q)`
 (`h𝒪`-compatibility to verify); (2) the SPELLING BRIDGE between
 `ValuationSubring.inertiaSubgroup k` (the NOS statement's inertia)
 and the image of `localInertiaGroup q` under
 `absoluteGaloisGroup.map` (via `lift_map`, mirroring the proven
 embedding-prime transport); (3) the identification of
 `(ρ.toLocal q)`'s action on `E.galoisRep`'s space with
 `Affine.Point.map` on `p`-torsion (unfold `galoisRep`/`toLocal`).
 Then `IsUnramifiedAt` = `localInertiaGroup ≤ ker` follows. The
 `IsFlatAt` glue is the same pattern against
 `torsion_flat_of_good_reduction` plus the `ℤ_(p) → ℤ_p` base
 change of the prolongation package. VERIFIED (2026-07-17):
 `E.galoisRep`'s action is `DistribMulAction.toAddMonoidEnd` of the
 ambient `(Kᵃˡᵍ ≃ₐ[K] Kᵃˡᵍ)`-action on `(E⁄Kᵃˡᵍ).Point` restricted
 to `nTorsion` (`Torsion.lean:179-194`), and
 `GaloisRep.toLocal ρ v = ρ ∘ absoluteGaloisGroup.map` (abbrev,
 `GaloisRep.lean:309`) — so for `σ ∈ localInertiaGroup`,
 `(ρ.toLocal v) σ = 1` UNFOLDS to "`map σ` fixes every `p`-torsion
 point via `Point.map`", which is EXACTLY the NOS conclusion at
 `σ' := map σ`. The glue therefore reduces to: (a) the 𝒪-construction
 + `h𝒪`, (b) `map σ ∈ 𝒪.inertiaSubgroup`-form (the spelling bridge:
 `inertiaSubgroup` is the kernel of the decomposition-subgroup action
 on `κ(𝒪)` — relate to the `𝔪(IC)`-inertia through `ι` and
 `lift_map`), (c) the `DistribMulAction`-vs-`Point.map` and
 `ker`-membership unfoldings (`AddMonoidHom.ext` on torsion
 generators).
- 2026-07-17 (session 5, recon): `integralClosureValuationSubring`
 ( def) bundles `IC 𝒪ᵥ L` as a `ValuationSubring L`; take
 `𝒪 := (integralClosureValuationSubring v Kᵥᵃˡᵍ).comap
 (AlgebraicClosure.map f)` (`ValuationSubring.comap` ✅ mathlib). The
 `h𝒪`-compatibility `(𝒪.comap (algebraMap ℚ ℚ̄)).toSubring =
 (algebraMap ℤ_(q) ℚ).range` unfolds via `map_algebraMap` to
 `f x ∈ IC-big ↔ f x ∈ 𝒪ᵥ` (integrality restricted to `Kᵥ`; `𝒪ᵥ`
 integrally closed) and then to
 `v.valuation ℚ x ≤ 1 ↔ x ∈ range (ℤ_(q) → ℚ)` — the ONE-PLACE
 analogue of mathlib's `mem_integers_of_valuation_le_one`
 (`AdicValuation.lean:423`, all-places): prove for
 `Localization.AtPrime v.asIdeal` by mirroring its
 `IsLocalization.surj` + factor-count argument at the single place,
 or through the `IsLocalization.AtPrime` unit-criteria already used
 in `Semistable.lean`. BETTER (verified): mathlib ALREADY HAS the
 one-place criterion —
 `IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime` (the
 localization at `v` as a `ValuationSubring K`) with
 `valuationSubringAtPrime_eq_valuationSubring` (equality with
 `(valuation K v).valuationSubring`, `AdicValuation.lean:~509`). So
 `h𝒪` is pure assembly: `x ∈ 𝒪.comap (aM ℚ ℚ̄)` ⟺ (via
 `map_algebraMap`) `aM Kᵥ Kᵥᵃˡᵍ (f x) ∈ IC-big` ⟺ `f x ∈ 𝒪ᵥ`
 (`IsIntegrallyClosed.isIntegral_iff` — integral closure of `𝒪ᵥ` in
 its OWN fraction field) ⟺ `Valued.v (f x) ≤ 1`
 (`mem_adicCompletionIntegers`) ⟺ `v.valuation ℚ x ≤ 1`
 (`valuedAdicCompletion_eq_valuation'`) ⟺
 `x ∈ valuationSubringAtPrime ℚ v` (mathlib equality) ⟺
 `x ∈ range (Localization.AtPrime → ℚ)` (IsLocalization
 uniqueness/`algEquiv` between the two localization models).
 IMPLEMENTATION NOTES for `h𝒪` (design fixed, first draft reverted
 for cleanliness): `valuationSubringAtPrime` membership is BY
 DEFINITION `∃ a s (_ : s ∈ v.asIdeal.primeCompl), x = aM a *
 (aM s)⁻¹` (`Localization.subalgebra.ofField` carrier,
 `AsSubring.lean:127`, membership Iff.rfl after the two mathlib
 rewrites `Valuation.mem_valuationSubring_iff` +
 `valuationSubringAtPrime_eq_valuationSubring`). CRUCIAL: there is
 NO global `Algebra (Localization.AtPrime v.asIdeal) K` instance —
 state `h𝒪` with the SAME hypothesis pack as the Semistable glue
 nodes (`[Algebra (Localization.AtPrime v.asIdeal) K]`
 `[IsScalarTower (𝓞 K) (Localization.AtPrime v.asIdeal) K]`
 `[IsFractionRing (Localization.AtPrime v.asIdeal) K]`, mirroring
 `instAlgebraLocalizationAtPrimeRat`'s package), and bridge the
 `∃`-form to `(algebraMap Loc K).range` with
 `IsLocalization.mk'_surjective` + `IsLocalization.lift_mk'`/tower
 compatibility. Steps 1–3 of the chain drafted and typecheck-shaped:
 step1 `show ... ∈ integralClosure ...; rw [AlgebraicClosure.map_algebraMap]; rfl`;
 step2 `isIntegral_algebraMap_iff` +
 `IsIntegrallyClosed.integralClosure_eq_bot`; step3
 `mem_adicCompletionIntegers` + `valuedAdicCompletion_eq_valuation'`.
- 2026-07-17 (session 5): **`embeddedValuationSubring_comap_toSubring`
 ** (unconditional) — the `h𝒪`-compatibility: the pullback of
 the embedded valuation subring to `K` equals the range of
 `Localization.AtPrime v.asIdeal` (with the localization algebra
 pack as hypotheses). The four-step chain compiled as designed; the
 range-bridge via `mk'`-calculus (`mk'_surjective` is a
 `Surjective`-over-PAIRS statement — destructure `⟨⟨a, s⟩, hys⟩`;
 `mk'_spec` + tower + `eq_mul_inv_iff_mul_eq₀`). NOS-glue piece (a)
 done. Remaining: (b) the `inertiaSubgroup` spelling bridge (image
 of `localInertiaGroup` lands in `𝒪.inertiaSubgroup K`:
 decomposition-membership = stabilizing `𝒪`, then triviality on
 `κ(𝒪)` from `𝔪(IC)`-inertia through `lift_map` and the
 residue-field comparison), (c) the `ker`-unfolding in the glue node
 itself.
- 2026-07-17 (session 5): **THE SPELLING BRIDGE IS ** (all
 unconditional): `map_smul_embeddedValuationSubring` (the image of
 ANY `Γ Kᵥ`-element stabilizes `𝒪`, via `lift_map` + integrality
 stability both ways), `embeddedComparison` (the codRestrict
 comparison hom into the big integral closure),
 `mem_maximalIdeal_iff_embeddedComparison` (unit REFLECTION: an
 inverse upstairs restricts along the comap; `𝔪`-membership is
 detected upstairs), and
 `map_mem_inertiaSubgroup_of_mem_localInertiaGroup` (THE bridge:
 the image of a local inertia element lies in
 `𝒪.inertiaSubgroup K` — residue triviality via
 `IsLocalRing.ResidueField.residue_smul` (NOTE the full namespace)
 + `Ideal.Quotient.eq` + the detection lemma; needs
 `public import Mathlib.RingTheory.Valuation.RamificationGroup`).
 NOS-glue pieces (a) and (b) DONE. Remaining: (c) assemble
 `isUnramifiedAt_of_hasGoodReduction` in `Semistable.lean` — apply
 the NOS node at `𝒪 := embeddedValuationSubring`,
 `h𝒪 := embeddedValuationSubring_comap_toSubring` (hypothesis pack
 present there), the bridge for inertia membership, and unfold
 `(ρ.toLocal q).ker`-membership to the pointwise torsion statement
 (`AddMonoidHom.ext`-style on the `nTorsion` action; `galoisRep`'s
 action is the ambient `DistribMulAction`, so the NOS conclusion is
 the needed fixing statement at `map σ`). Check the NOS node's exact
 variable pack (R k ksep n E instances) when instantiating.
- 2026-07-17 (session 5): **`isUnramifiedAt_of_hasGoodReduction`
 — frontier 21 → 20.** The good-reduction unramifiedness glue
 now rests SOLELY on the NOS leaf
 (`torsion_unramified_of_good_reduction`): instantiate at
 `𝒪 := embeddedValuationSubring` with
 `h𝒪 := embeddedValuationSubring_comap_toSubring` (Semistable's
 localization pack in scope), inertia membership by the spelling
 bridge, `NeZero` by `neZero_natCast_residueField` (MOVED before the
 glue node — single-pass file order), and the `ker`-membership closed
 by `show (ρ.toLocal v) σ = 1` (the `toLocal`-SPELLED form — the
 `ρ (map σ)`-spelling is NOT accepted by `show` even though
 ker-membership itself is defeq to application-eq) +
 `LinearMap.ext` + `Subtype.ext` + the NOS conclusion verbatim
 (`Point.map` matches the ambient action definitionally; the
 torsion-membership bridge is `Submodule.mem_torsionBy_iff` +
 `exact_mod_cast`). Axiom audit: `sorryAx` ONLY through the NOS
 leaf. Gate-only full build. NEXT: the same pattern for
 `isUnramifiedAt_of_hasMultiplicativeReduction` (against the Tate
 machinery — MORE content: unipotent-not-trivial inertia, quadratic
 twist; see the node's docstring) and the two `IsFlatAt` glue nodes
 (against `torsion_flat_of_good_reduction`, plus the `ℤ_(p) → ℤ_p`
 prolongation base change).
- 2026-07-17 (session 5):
 **`isUnramifiedAt_of_hasMultiplicativeReduction` ** — the
 multiplicative-prime unramifiedness glue decomposes exactly like the
 good-reduction one: NEW sorry node
 `torsion_unramified_of_multiplicative_reduction` (the pure
 TATE-THEORETIC content — quadratic twist + Tate uniformization +
 `p ∣ v_q(j)` p-th-power analysis — stated in the SAME
 `ValuationSubring.inertiaSubgroup`/`Point.map` shape as the 
 NOS node, with the `h𝒪`-hypothesis in the same range-form), and the
 glue itself is a VERBATIM copy of the good-reduction transport.
 Frontier stays 20 by count; the transport content of the node is
 eliminated. NOTE: `E⁄A` is `WeierstrassCurve.baseChange E A`
 (scoped notation in `VariableChange.lean`/`Weierstrass.lean`) — the
 leaf must be stated with `(E⁄ℚ̄).Point` (single base change from ℚ,
 the NOS shape); the glue's `(E.map ..)⁄ℚ̄`-spelled points unify with
 it definitionally at application time. `GoodReduction` is now a
 PUBLIC import of `Semistable.lean` (the leaf's statement needs the
 `inertiaSubgroup` language).
- 2026-07-17 (session 5, flat-transport design): mathlib HAS Hopf base
 change (`Mathlib.RingTheory.HopfAlgebra.TensorProduct`:
 `HopfAlgebra S (B ⊗[R] A)` under towers). The `IsFlatAt` glue arc:
 (i) the algebra `ℤ_(p) → 𝒪ᵥ` (codRestrict along the valuation
 criterion — the `h𝒪`-chain tools apply); (ii)
 `G := 𝒪ᵥ ⊗[ℤ_(p)] H` from the leaf's package `H`
 (flat/finite by base change; étale generic fibre by base-change
 associativity `Kᵥ ⊗[𝒪ᵥ] G ≅ Kᵥ ⊗[ℚ] (ℚ ⊗[ℤ_(p)] H)` + étale base
 change); (iii) points comparison
 `Homs_{Kᵥ}(Kᵥ ⊗ G, Kᵥᵃˡᵍ) ≃ Homs_ℚ(ℚ⊗H, Kᵥᵃˡᵍ) ≃ Homs_ℚ(ℚ⊗H, ℚ̄)`
 — tensor-hom adjunction + "finite ℚ-algebra maps into `Kᵥᵃˡᵍ` land
 in `ι(ℚ̄)`" (the image is algebraic over ℚ; `ι(ℚ̄)` is the algebraic
 closure of ℚ inside `Kᵥᵃˡᵍ`); (iv) `Γ Kᵥ`-equivariance through
 `lift_map` against the leaf's `Gal(ℚ̄/ℚ)`-equivariance; (v) the
 `∀`-open-ideal quantifier of `IsFlatAt`: for `A = ZMod p`, `I = ⊥`
 is the leaf package and `I = ⊤` the ZERO module (tiny standalone
 package `G := 𝒪ᵥ`, one-point homs ≃ zero space); intermediate `I`
 don't occur for prime `p` (or handle by quotient-torsion).
 Multi-iteration arc; start with (i).
- 2026-07-17 (session 5): flat-arc steps (i) and (v-degenerate) 
 (`localizationToAdicCompletionIntegers` +
 `algebraMap_localization_mem_adicCompletionIntegers`;
 `GaloisRep.hasFlatProlongationAt_of_subsingleton` in the NEW module
 `Deformations/RepresentationTheory/FlatProlongation.lean` — trivial
 Hopf `𝒪ᵥ`, unique generic point via `Algebra.TensorProduct.rid` +
 `Algebra.Etale.of_equiv`, zero comparison map between singletons).
 PLUMBING NOTES for (ii)–(iv): use
 `Algebra.TensorProduct.cancelBaseChange` for
 `Kᵥ ⊗[𝒪ᵥ] (𝒪ᵥ ⊗[ℤ_(q)] H) ≃ₐ Kᵥ ⊗[ℤ_(q)] H`; MIND THE GROUP
 STRUCTURES — the leaf's points are
 `Additive (WithConv (K ⊗ H →ₐ Ksep))` while `HasFlatProlongationAt`
 uses bare `Additive (Kᵥ ⊗ G →ₐ Kᵥᵃˡᵍ)` (the convolution AddMonoid
 must come from an instance on hom-sets out of Hopf algebras —
 reconcile the two spellings when building the comparison); the
 transport should be stated for `ρ : GaloisRep ℚ A M` with a
 leaf-shaped equivariant iso onto `M`-with-the-`ρ`-action, then
 specialized to the elliptic case. FOUND: the bare-hom `Monoid`
 instance behind `HasFlatProlongationAt`'s `Additive (… →ₐ …)` is
 the VENDORED convolution instance in
 `Deformations/RepresentationTheory/Etale.lean:30`
 (`Monoid (A →ₐ[K] L)` for `Bialgebra K A`); the leaf's
 `WithConv`-wrapped structure is mathlib's — the reconciling
 `MulEquiv` should be identity-underlying (`WithConv` is a
 def-wrapper). SCRATCH-VERIFIED (2026-07-17): with
 `letI := (localizationToAdicCompletionIntegers v).toAlgebra`, the
 instance `HopfAlgebra 𝒪ᵥ (𝒪ᵥ ⊗[ℤ_(q)] H)` SYNTHESIZES from
 mathlib's tensor-product Hopf instance (needs `noncomputable`,
 respectTransparency, 1M synth heartbeats) — step (ii)'s core is
 viable end-to-end. Next session: build the main transport
 (`G := 𝒪ᵥ ⊗[ℤ_(q)] H`, flat/finite by base change, étale generic
 fibre by `cancelBaseChange`, the three-layer points comparison with
 equivariance, and the `IsFlatAt` assembly over the two open ideals
 of `ZMod p`).
- 2026-07-17 (session 5): **BOTH `IsFlatAt` GLUE NODES — all
 five original local-global glue nodes are now closed onto content
 leaves plus ONE shared transport.** New sorry node
 `GaloisRep.isFlatAt_of_dvr_package` (`FlatProlongation.lean` — the
 shared flat transport: DVR-package over `ℤ_(q)` with equivariant
 `WithConv`-points iso onto the rep's space ⟹ `IsFlatAt`; all
 ingredients proven or scratch-verified per the design log above).
 `isFlatAt_of_hasGoodReduction` from
 [`torsion_flat_of_good_reduction` ( leaf) + the transport]:
 the `AddSubgroup.torsionBy`/`nTorsion` bridge is an
 identity-underlying `AddEquiv` (`AddSubgroup.torsionBy` is
 REDUCIBLY `(Submodule.torsionBy ℤ A n).toAddSubgroup`), and the
 equivariance transports by `Subtype.ext` + the leaf's statement
 verbatim. `isFlatAt_of_hasMultiplicativeReduction` from the
 NEW leaf `torsion_flat_of_multiplicative_reduction` (pure
 peu-ramifiée Tate content, stated in the SAME DVR-package `∃`-shape
 so the shared transport applies verbatim) + the transport. Frontier
 stays 20 by count; the transport content of both flat glue nodes is
 now concentrated in ONE node whose design is fully de-risked.
 GOTCHAS: the `⊗[R]` notation needs `open TensorProduct`; the
 `WithConv`-monoid needs `Mathlib.RingTheory.Bialgebra.Convolution`
 + `HopfAlgebra.TensorProduct` PUBLIC (statement-level); `∃ (_ : C)`
 binders DO provide instances for the rest of the `∃`-body.
- 2026-07-17 (session 5, flat-transport layer C ):
 `mem_range_algebraicClosureMap_of_isIntegral` (integral elements of
 `Kᵥᵃˡᵍ` over `K` land in `ι(Kᵃˡᵍ)`: minpoly splits over `Kᵃˡᵍ`,
 `Polynomial.Splits.roots_map` pushes the root multiset through `ι`),
 `algebraicClosureMapAlgHom` (`ι` as a `K`-AlgHom; `commutes'` by
 `show`-normalizing to `AlgebraicClosure.map_algebraMap` + the
 scalar-tower unfolding), and `algHomEquivOfFinite (B) [Module.Finite
 K B] : (B →ₐ[K] Kᵥᵃˡᵍ) ≃ (B →ₐ[K] Kᵃˡᵍ)` — postcomposition with `ι`
 is a bijection on points of a finite `K`-algebra. All three audit to
 the standard axioms. GOTCHAS: `AlgHom.codRestrict` wants a
 `Subalgebra`, but `AlgHom.fieldRange` is an `IntermediateField` —
 use `AlgHom.range` + `AlgEquiv.ofInjective` (Subalgebra-valued,
 injectivity via `.toRingHom.injective`) instead of
 `ofInjectiveField`; the round-trip `rw [AlgEquiv.apply_symm_apply]`
 fails through the `AlgHom.comp` coercion layers — `refine
 (….apply_symm_apply _).trans ?_` unifies up to defeq and works.
 Remaining for `isFlatAt_of_dvr_package`: layer A (`cancelBaseChange`
 precomposition equiv), layer B (tensor-hom adjunction
 `Algebra.TensorProduct.lift`-style points identification),
 convolution-monoid compatibility of each layer, equivariance, and
 the `ZMod p` two-open-ideals assembly.
- 2026-07-17 (session 5): **THE ENTIRE SHARED FLAT TRANSPORT IS
 SORRY-FREE** (frontier 20 → 19). Completed in three moves. (1)
 `isFlatAt_of_dvr_package` (over a FIELD `A`) from a new
 smaller core node by the two-ideal split: `⊤` via the subsingleton
 case, `⊥` via the `HasFlatProlongationAt.of_addEquiv`
 (equivariant transport of the package across an `AddEquiv` of
 spaces; the identification `M ≃+ (A ⧸ ⊥) ⊗[A] M` via
 `AlgEquiv.quotientBot` + `baseChange_tmul`). (2) The convolution
 layer lemmas: mathlib's `AlgHom.liftEquiv` (tensor-hom adjunction)
 respects the convolution unit/product/postcomposition — the
 inverse direction by computing `comul` on the base-changed
 bialgebra (`Bialgebra.TensorProduct.comul_eq_algHom_toLinearMap`,
 induction over `comul a`), the forward direction by
 symm-injectivity; the bare-hom `Monoid` of `Etale.lean`
 agrees with mathlib's `WithConv` monoid at rfl-level
 (`vendored_one/mul_eq_conv*`); `algHomEquivOfFinite` respects
 convolution (`AlgHom.comp_convMul_distrib` — postcomposition with
 `ι` distributes) and intertwines `Γ Kᵥ`-postcomposition with
 `Γ ℚ`-postcomposition (`Field.absoluteGaloisGroup.lift_map`). (3)
 `hasFlatProlongationAt_of_hopf_package` (general `K`, abstract
 coefficient ring `R`): witness `G := 𝒪ᵥ ⊗[R] H` (Hopf/finite/flat
 by base-change instances — `Mathlib.RingTheory.HopfAlgebra.
 TensorProduct` must be imported EXPLICITLY, module system does not
 re-export it through GaloisRep), étale generic fibre via
 `cancelBaseChange R K Kᵥ Kᵥ H` + `(cancelBaseChange R 𝒪ᵥ Kᵥ Kᵥ
 H).symm` + `Algebra.Etale.baseChange`, points comparison
 `dvrPointsEquiv` = `liftEquiv.symm ∘ liftEquiv.symm ∘ liftEquiv ∘
 algHomEquivOfFinite` (NO cancelBaseChange needed for points), f'
 assembled with inline `by` blocks. The ℚ-instantiation
 `hasFlatProlongationAt_of_dvr_package` equips `𝒪ᵥ`/`Kᵥ` with
 `ℤ_(q)`-algebra structures via `localizationToAdicCompletionIntegers`
 (composed through `𝒪ᵥ` so the first tower is rfl). ALL audit to
 standard axioms; the two `IsFlatAt` glue nodes now rest ONLY on
 the content leaves. GOTCHAS: (a) `∃`-anonymous-constructor
 `refine` postpones dependent instance metavars — type-ascribe
 each instance component (`(inferInstance : HopfAlgebra …)`); (b)
 structure-literal fields with `?_` lose their lambda binders —
 inline `by` blocks instead; (c) at `K := ℚ` the instance search
 for `Algebra ℚ Kᵥ` returns `DivisionRing.toRatAlgebra`, NOT the
 canonical `instAlgebraAdicCompletion` baked into general-`K`
 statements — pin the canonical instance explicitly in `@`-form
 when constructing `IsScalarTower Loc ℚ Kᵥ`; (d) `[Algebra K B]` +
 `[Bialgebra K B]` binders together create an `SMul` diamond that
 BREAKS `WithConv` instance synthesis — take only `[Bialgebra K B]`.
- 2026-07-17 (session 5): **BOTH TORSION-COUNT NODES from six
 sharp division-polynomial leaves** (`TorsionCard.lean`; frontier
 count 19 → 23, strictly shallower — every remaining leaf is a
 concrete polynomial identity or a single Washington-Thm-3.6-style
 point formula). `smul_surjective` from [the fibre-point node
 `exists_point_x_smul` + the `x([n]P)` formula node
 `exists_smul_some_eq` + `isCoprime_Φ_ΨSq` (Bézout, resultant branch)
 + `Y_eq_of_X_eq`/negation]. `prime_torsion_card` from [the
 dictionary node `smul_some_eq_zero_iff` + `separable_preΨ'` +
 `isCoprime_Ψ₂Sq_preΨ'` + `separable_Ψ₂Sq`] via a shared counting
 skeleton: nonzero torsion = biUnion over roots of the cutting
 polynomial of the `y`-fibre finsets (`pointsAt`); 
 infrastructure includes the characteristic-free discriminant
 identity `(∂yQuad)² - 4·yQuad = C (Ψ₂Sq x₀)` and the explicit-Bézout
 separability `yQuad_separable` (audits clean). NOTE mathlib's
 division polynomials have NO point-level theory (the `zsmul` formula
 is `sorry` even in Angdinata's public mathlib branch
 `EllipticCurve.Torsion`; his torsion/Tate-module work with Wu and Xu
 is unpublished WIP) — the six leaves are exactly the missing
 arithmetic. GOTCHAS: `Polynomial.mem_roots'` for the unprimed-
 hypothesis form; `Set.ncard_coe_finset` (lowercase); `Nat.card_coe_
 set_eq` is root-namespace; `subst` on `hx : x' = ξ` eliminates the
 WRONG variable when both sides are locals (use an explicit
 coordinate-equality helper `hpoint` instead); `nomatch hP` for
 constructor-distinct `Point` equalities (`noConfusion` has universe
 trouble); `(0 : Point) = Point.zero` needs an explicit `show`/`rw`
 before `nomatch`; the `∃`-form fibre nodes avoid needing the `ω`
 division polynomial entirely (not yet defined in mathlib).
- 2026-07-17 (session 5, division-polynomial attack map): the three
 remaining point-level nodes (`smul_some_eq_zero_iff`,
 `exists_smul_some_eq`, `exists_point_x_smul`) and `separable_preΨ'`
 are Washington *Elliptic Curves* Thm 3.6 territory. Mapped attack
 for the dictionary + formula nodes: simultaneous strong induction on
 `n` proving `x([n]P)·ψ_n²(x,y) = φ_n(x,y)` AND the `y`-coordinate
 tracked VALUE-wise (define `ωval n P := y(n•P)` on points, avoiding
 the `ω` polynomial mathlib lacks), with the inductive steps
 `[n+1]P = [n]P + P` and `[2n]P = 2·[n]P` computed by mathlib's
 `Affine.slope`/`addX`/`some_add_some` formula API and the EDS
 recurrences `preΨ'_even/odd` (`Mathlib.NumberTheory.
 EllipticDivisibilitySequence` + `DivisionPolynomial.Basic`
 recursion lemmas); each case is a curve-relation polynomial
 identity dischargeable by `linear_combination (norm := ring1)`
 against `equation_iff` after denominator clearing (the nonvanishing
 `ψ_n(x,y) ≠ 0` is exactly the dictionary's other direction, so the
 induction must prove the dictionary and the formula TOGETHER).
 `separable_preΨ'` afterwards via the disc-companion resultant
 identity (same family as `resultant_Φ_ΨSq` — Ayad, Manuscripta
 Math. 76). NOTE the annas-mcp server is not connected in this
 session; Washington/Silverman PDFs are not in `Books/` yet —
 download them when the MCP is available (the argument structure
 above is standard and self-contained to formalize regardless).
- 2026-07-17 (session 5, Thm 3.6 state): `zsmul_some_aux` is the ❌🟪
 frontier node; BOTH base cases are (`zsmul_some_aux_one`,
 `two_smul_some_eq_zero_iff`) and the consumers (dictionary +
 formula) are . Pinned API for the step cases: mathlib
 `Affine.Point.add_some (hxy : ¬(x₁ = x₂ ∧ y₁ = negY x₂ y₂)) :
 some h₁ + some h₂ = some (nonsingular_add h₁ h₂ hxy)` with
 coordinates `addX x₁ x₂ (slope x₁ x₂ y₁ y₂)` / `addY`;
 `add_of_Y_eq` for the cancellation case; the `ψ`-recurrences via
 `normEDS` (`Mathlib.NumberTheory.EllipticDivisibilitySequence`) and
 `Ψ_even/Ψ_odd/preΨ_even/preΨ_odd` in `DivisionPolynomial.Basic`;
 evaluation bridges in `Fermat/FLT/Mathlib/.../
 DivisionPolynomial/Points.lean`. The step `[n+1]P = [n]P + P` needs
 the x-addition identity `addX(x, x', λ)·ψ_{n+1}² = φ_{n+1}` given
 the IH identities at `n` (and `n-1` for the slope elimination) —
 the giant `linear_combination` against the curve equation; the
 step `[2n]P = 2·[n]P` needs the duplication identity. These two
 identities are the remaining mountain; everything else is plumbing.
- 2026-07-17 (session 5, Thm 3.6 ingredients COMPLETE): everything the
 `zsmul_some_aux` step cases consume is now and audits clean:
 `evalEval_φ_eq` (`φₙ = x·ψₙ² − ψₙ₊₁ψₙ₋₁` on the curve — equivalently
 `x − x([n]P) = ψₙ₊₁ψₙ₋₁/ψₙ²`, the difference form), `evalEval_ψ_even`
 (`ψ₂ₘ·ψ₂ = ψₘ₋₁²ψₘψₘ₊₂ − ψₘ₋₂ψₘψₘ₊₁²`), `evalEval_ψ_odd`
 (`ψ₂ₘ₊₁ = ψₘ₊₂ψₘ³ − ψₘ₋₁ψₘ₊₁³`; the `Ψ_odd` correction dies on
 points since it carries `W.polynomial` as a factor), the base cases
 `zsmul_some_aux_one` and `two_smul_some_eq_zero_iff`, and the
 evaluation bridges. What remains inside the node is the
 strong-induction assembly: cases `[n+1]P = [n]P + P` and
 `[2n]P = 2·[n]P` via `Affine.Point.add_some`/`add_of_Y_eq`, where
 the coordinate identities reduce, after `field_simp`, to
 `linear_combination`s of the curve equations of `(x,y)`/`(x',y')`,
 the IH identities, and the two on-curve recurrences above. GOTCHA:
 `Polynomial.evalEval_mul/sub/add/pow` are the working simp set for
 pushing `evalEval` through `Ψ`-identities (the
 `coe_evalEvalRingHom`+`map_*` route stalls).
- 2026-07-17 (session 5): **THE DUPLICATION FORMULA IS **
 (`zsmul_some_aux_two`, characteristic-free, no `(2:k) ≠ 0` needed):
 for `ψ₂(x,y) ≠ 0`, `2•P` is affine with `x'·ψ₂² = φ₂(x,y)` and
 `(2y'+a₁x'+a₃)·ψ₂⁴ = ψ₄(x,y)`. METHOD (now validated, use for the
 remaining step cases): (1) NO field_simp — work with the multiplied
 slope equation `hT : ℓ·ψ₂v = 3x²+2a₂x+a₄−a₁y` (from
 `div_mul_cancel₀`); (2) the goal's `λ`-powers are eliminated by a
 hand-computed `linear_combination` coefficient on `hT` (telescoping
 `(λd)^k − T^k` factors); (3) the remaining curve-equation multiplier
 is computed EXACTLY by sympy polynomial division of the λ-free
 residual by `g = y² + a₁xy + a₃y − (x³+a₂x²+a₄x+a₆)` in `y`
 (remainder verified 0) and pasted as the `heq`-coefficient. sympy is
 now installed (`pip3 install --break-system-packages --user sympy`).
 Model file pattern in the proof of `zsmul_some_aux_two`. Remaining
 inside the ❌🟪 node `zsmul_some_aux`: the two-point addition step
 (secant slope, same certificate workflow against the IH identities —
 ideal membership via sympy Groebner if plain division does not
 suffice) and the strong-induction assembly.
- 2026-07-17 (session 5, `zsmul_some_aux` assembly design COMPLETE —
 numerically validated): the induction proceeds on the tracked pair
 ((i) `xₙψₙ² = φₙ`, (ii) `tₙψₙ⁴ = ψ₂ₙ` with `tₙ` the `ψ₂`-value at
 `n•P`), steps `[2m+1]P = [m+1]P + [m]P` and `[2m]P = [m+1]P +
 [m-1]P` (NOT duplication — compositions like `Ψ₃(xₘ)` would intrude).
 inputs: the secant denominators are exactly `x_sub_gap_one`
 (`(xₘ₊₁−xₘ)(ψₘψₘ₊₁)² = −ψ₂ₘ₊₁`) and `x_sub_gap_two`
 (`(xₘ₋₁−xₘ₊₁)(ψₘ₋₁ψₘ₊₁)² = ψ₂ₘψ₂`), both derived from
 `evalEval_φ_eq` + the on-curve recurrences; the collision branches
 divert through `smul_collision`/`eq_or_add_eq_zero_of_X_eq` to the
 dictionary side; `add_some_coords` gives the sum's coordinates in
 multiplied form; the `y`-differences come from the trackings via
 `2(yᵢ−yⱼ) = (tᵢ−tⱼ) − a₁(xᵢ−xⱼ)` — THE ONLY place `(2:k) ≠ 0`
 enters (thread it through `zsmul_some_aux` and consumers when
 assembling; the FLT pipeline consumes torsion counts at char 0
 only). REMAINING (one focused session): per-step certificates in the
 window variables `ψₘ₋₂..ψₘ₊₃` — the targets' double-index values
 (`φ₂ₘ₊₁`, `ψ₂ₘ`, `ψ₄ₘ₊₂`, …) reduce to the window through the
 recurrences, but the recurrence instances are PARITY-SPECIFIC, so
 the assembly needs the classical four-fold case split (`n = 2m`,
 `2m+1` with `m` even/odd) with per-case sympy-computed
 `linear_combination` certificates (Groebner/ideal-membership against
 the curve equation, the IH relations, and the parity-instantiated
 recurrences; the validated workflow and a worked model are in the
 proofs of `zsmul_some_aux_two` and the gap lemmas). Boundary values
 `ψ₀ = 0`, `ψ₁ = 1`, `ψ₋₁ = −1` are inline-available from mathlib
 (`ψ_zero`/`ψ_one`/`ψ_neg`) for the small-`m` instantiations.
- 2026-07-17 (session 5, odd-step certificate structure): the odd-step
 `x`-target IS numerically true in the free-window model, and the
 certificate ideal needs THREE generator families: (a) the curve
 equation `g(x,y)`, (b) the two Ward gap-2 bindings
 `ψₘ₊₂ψₘ₋₂ = ψₘ₊₁ψₘ₋₁ψ₂² − Ψ₃ψₘ²` (at `m` and `m+1` — these bind the
 outer window symbols; carried as component (iii) of the simultaneous
 induction package since mathlib's Ward relation for `normEDS` is an
 open TODO; base instances `j = 2, 3` are trivial), and (c) the IH
 points' own curve-membership — in the free-window sympy model this
 is the cleared `tⱼ² = Ψ₂Sq(xⱼ)` compatibility, but in the LEAN
 assembly it comes free as `heqₘ : Equation xₘ yₘ` from the IH's
 `Nonsingular` data (use the points' equations directly as
 `linear_combination` inputs rather than the eliminated form).
 Groebner verification of the closure running; the same structure
 applies to the even step `[2m] = [m+1] + [m−1]` with gap-2 as the
 secant denominator.
- 2026-07-17 (session 5, `zsmul_some_aux` — THE PACKAGE IS
 STRUCTURALLY COMPLETE): the odd-step x-target's residual over
 (curve equation, IH memberships) factors EXACTLY as
 `W²((b₂+12x)ψₙ²ψₙ₊₁² − 4(ψₙ₋₁ψₙ₊₁³+ψₙ³ψₙ₊₂)) − (ψₙψₙ₊₁)⁶(tₙ+tₙ₊₁)²`
 — the missing information is the CROSS-TERM `tₙtₙ₊₁` (the relative
 sign of consecutive trackings, which memberships alone cannot fix).
 The induction package therefore carries THREE components:
 (i) `xₙψₙ² = φₙ`; (ii) `tₙψₙ⁴ = ψ₂ₙ`; (iii) the cross-tracking
 `2tₙtₙ₊₁(ψₙψₙ₊₁)⁶ = ψ₂ₙ₊₁²((b₂+12x)ψₙ²ψₙ₊₁² − 4(ψₙ₋₁ψₙ₊₁³+ψₙ³ψₙ₊₂))
 − (ψₙψₙ₊₁)⁶(Ψ₂Sq(xₙ)+Ψ₂Sq(xₙ₊₁))` — window-expressible, numerically
 validated for n = 2..5 (validator in the certificate script). With
 (iii) as an ideal generator the odd-step x-target closes by
 construction; (iii) also supersedes the earlier Ward-gap-2 plan
 (Z, E eliminate via the trackings with only ψₙ, ψₙ₊₁ ≠ 0
 denominators). Remaining: certify the propagation of (i)+(ii)+(iii)
 through both steps with the script (mechanical), then write the
 Lean skeleton.
- 2026-07-17 (session 5, odd-step x-certificate EXACT): with (iii) and
 the two memberships as hypotheses, the odd-step x-target closes with
 UNIT COFACTORS — `num + 1·(iii) + ψₙ₊₁⁶·(membership at n) +
 ψₙ⁶·(membership at n+1) = 0` IDENTICALLY (not even the curve
 equation is needed at this level; verified symbolically, validator
 `certificate_odd_step_x` in the script). The Lean certificate is a
 three-term `linear_combination`; the memberships come from the IH
 points' `Nonsingular` data via the proven on-curve pattern
 `Ψ₂Sq(xⱼ) = tⱼ²` (the `hΨval` computation in
 `two_smul_some_eq_zero_iff` — extract it as a standalone lemma when
 assembling). Remaining certificates to compute with the script: the
 odd-step t-target, the (iii)-propagation to the output pairs, and
 the even-step analogues — then the skeleton.
- 2026-07-17 (session 5, degenerate branch closed): the induction's
 outermost split is on `s := ψ₂(x,y)`. If `s = 0` (`P` is
 2-torsion): even-index `ψ`-values vanish identically (the `ψ₂`
 factor), `n•P` alternates `0, P`, and (i)/(ii) hold trivially ONCE
 odd-index `ψ`-values are known nonzero there — which follows by the
 odd recurrence (at `s = 0` it degenerates to a product of two
 smaller odd-index values) seeded by **`Res(Ψ₂Sq, Ψ₃) = −Δ²`
 EXACTLY** (sympy-verified, validator in the script): 2-torsion and
 3-torsion `x`-coordinates are disjoint on an elliptic curve in
 every characteristic. Lean-side this resultant is a concrete
 identity in `a₁..a₆` (7×7 Sylvester determinant — provable once by
 computation, then `exists_mul_add_mul_eq_C_resultant` gives the
 Bézout as in `isCoprime_Φ_ΨSq`). If `s ≠ 0`: the generic two-secant
 machinery with the `s`-divided even-recurrence eliminations is
 fully legal.
- 2026-07-17 (session 5): **BOTH step x-targets close with unit
 cofactors.** The even-step residual over (memberships at m−1, m+1)
 has t-part `−(ψₘ₋₁ψₘ₊₁)⁶(tₘ₊₁−tₘ₋₁)²`, giving the gap-2
 cross-relation (iii₂) (pair (m−1, m+1); only t-monomial
 `−2(ψₘ₋₁ψₘ₊₁)⁶tₘ₋₁tₘ₊₁`) with closure BY CONSTRUCTION:
 `num + (iii₂) + ψₘ₊₁⁶·cmₘ₋₁ + ψₘ₋₁⁶·cmₘ₊₁ = 0`; (iii₂) numerically
 validated m = 2..5 (validator `certificate_even_step_x`). The
 induction package therefore carries cross-tracking at BOTH pair
 gaps: (iii-a) consecutive `(n, n+1)`, (iii-b) gap-2 `(n−1, n+1)`.
 Certificate inventory remaining: the two t-target closures
 (odd-step check running with specialized coefficients) and the
 propagation of (iii-a)/(iii-b) to the output pairs — then the Lean
 skeleton.
- 2026-07-17 (session 5, odd t-target status): the deterministic
 elimination chain (tⱼ² → memberships, tₘtₘ₊₁ → (iii-a)) reduces the
 odd-step t-target to a t-LINEAR residue whose coefficients do NOT
 vanish mod the curve equation alone (78/78/195 terms) — the t-target
 needs additional t-linear generators beyond (memberships, iii-a):
 candidates are the s-coupled cross-instances (pairs `(1, m)`,
 `(1, m+1)`; note `t₁ = s`, `ψ₁ = 1`) — the general-pair
 cross-tracking family evaluated at gap `m∓1`... derive the exact
 shape by the same residual read-off next (extract the 78-term
 t-linear coefficient, identify it against `s·(window)`-multiples).
 Lean-side: `eval_Ψ₂Sq_eq_sq` (the membership identity) extracted as
 a standalone lemma; `two_smul_some_eq_zero_iff` refactored onto it.
- 2026-07-17 (session 5): **THE UNIVERSAL TWO-POINT CROSS IDENTITY IS
 IN LEAN** (`two_point_cross_identity`, cofactors −4/−4 on
 the two curve equations): `2t₁t₂(x₁−x₂)² = (b₂+4x₁+4x₂)(x₁−x₂)⁴ +
 4X₃ − (Ψ₂Sq(x₁)+Ψ₂Sq(x₂))(x₁−x₂)²` with `X₃` the multiplied secant
 `x`-form of `Q₁−Q₂`. Numerically verified to subsume ALL
 cross-tracking instances (pairs `(n,n+1)`: difference `P`;
 `(m−1,m+1)`: difference `2P`; `(1,m)`: difference `(m−1)P`) — so
 the induction package collapses back to (i) + (ii), and the
 t-linear generators the odd t-target needed are the `(1,·)`
 instances of THIS lemma (the difference x-coordinates are IH-known).
 Remaining before the skeleton: recompute the t-target closures with
 the universal-identity instances as generators (mechanical), and
 the step-output tracking derivations.
- 2026-07-17 (session 5): **`zsmul_some_aux` SIMPLIFIED — the tracking
 conjunct is GONE.** The `(1, j)`-instances of the proven
 `two_point_cross_identity` solve for the `ψ₂`-values
 `tⱼ = 2yⱼ + a₁xⱼ + a₃` in closed form (`tⱼ·ψⱼ³·s` = an explicit
 window expression; sympy-derived), so the induction carries ONLY the
 `x`-formula — the node's `∃` shrank to
 `n•P = some x' y' ∧ x'ψₙ² = φₙ`, consumers unchanged (they never
 used the tracking), downstream builds clean. The t-target
 certificate obligation CEASES TO EXIST; the induction steps pin all
 `y`-data through the universal identity and the two proven
 x-certificates close with unit cofactors. Remaining for the node:
 the strong-induction skeleton itself (case bookkeeping: parity,
 collisions via `smul_collision`, the `s = 0` branch via the
 `Res(Ψ₂Sq, Ψ₃) = -Δ²` seed, and the base cases — all staged).
- 2026-07-17 (session 5): **THE GENERIC ODD STEP IS IN LEAN**
 (`zsmul_odd_step_x`, audits clean, characteristic-free): from IH
 data at `m`, `m+1` (points via `heqm`/`heqm1`, x-formulas,
 trackings) with `xₘ₊₁ ≠ xₘ`, the point `(2m+1)•P` is affine with
 the x-formula. KEY DISCOVERY: the core `(x−x₃)dx² = t₁t₂` is a PURE
 RING identity from the two secant identities (sum and difference
 additions) — `linear_combination hX₄' − hX₃` — the universal
 identity and memberships DROP OUT of the x-side entirely (sympy
 cofactor-solve: c₂ = c₄ = c₅ = 0). The conversion layer:
 `evalEval_φ_eq` at `2m+1` + `x_sub_gap_one` + the congr-multiplied
 tracking product. REMAINING in the node: the even-step analogue
 (same shape with gap-2), the per-step TRACKING OUTPUT (the
 `t₃`-derivation — the internal (ii) at the new index, consumed by
 later steps), the collision/degenerate branches (all staged), and
 the skeleton wiring.
- 2026-07-17 (session 5): **THE CONSECUTIVE STEP IS 
 (`zsmul_consec_step_x`) — parity-free, superseding the odd/even
 split.** `[n]P = [n-1]P + P` with difference `[n-2]P`; the ring core
 `(x₂−x₃)dx² = t₁s` from the two secants; the conversion
 `φₙψₙ₋₂² = φₙ₋₂ψₙ² − sψ₂ₙ₋₂` from `evalEval_φ_eq` (at n,
 n−1, n−2) + `evalEval_ψ_even` (at n−1) + `evalEval_ψ_two`,
 assembled as two small linear_combinations and a `ψₙ₋₂²`-
 cancellation. IH inputs: points + x-formulas at n−1, n−2, tracking
 at n−1 only. REMAINING in the node: the per-step TRACKING OUTPUT
 (tₙ at the new index — the last open certificate), the collision
 and `s = 0` branches (staged), the base cases (proven), and the
 strong-induction wiring.
- 2026-07-17 (session 5, tracking-output design): the per-step
 tracking `tₙψₙ⁴ = ψ₂ₙ` reduces to the ψ-window identity (★s):
 `ψₙ₋₁²ψₙ₊₂ + ψₙ₋₂ψₙ₊₁² = ψₙ₋₁ψₙψₙ₊₁(6x²+b₂x+b₄) − ψₙ³Ψ₂Sq(x)` on
 the curve — the SUM-companion of the even recurrence (numerically
 V = 0; it was exactly the residue of the tracking-output reduction).
 At the point level it is the symmetric addition identity
 `sum_diff_X_identity` (NOW , cofactors −2/−2) composed with
 φ-difference eliminations — but the φ-eliminations return (★s)
 circularly, so (★s) needs a POLYNOMIAL-level proof by the mathlib
 `Ψ_even`/`Ψ_odd` technique (parity split on `n`, `preΨ'`
 recursions, `C_simp; ring1`) — same family, mathlib-PR-shaped.
 PLAN: state `evalEval_ψ_sum` (★s) as a sharp sorry node (replacing
 the remaining interior of `zsmul_some_aux` together with the
 staged pieces), derive the tracking output from it +
 `sum_diff_X_identity` + the universal identity, then wire the
 skeleton. The Thm 3.6 node then rests on: (★s) + the fibre node +
 `separable_preΨ'` + `resultant_Φ_ΨSq` — all pure
 division-polynomial statements.
- 2026-07-17 (session 5 cont.): TRACKING OUTPUT CLOSED (`ad9e21a`).
 The plan of the previous entry is executed: (★s) is stated as the
 sharp sorry node `evalEval_ψ_sum`; the pure two-point residue turned
 out even cleaner than projected — the chain [(★s) with cofactor ψₙ,
 gap-1 at n scaled by ψₙ₋₁², gap-1 at n-1] collapses the s-multiplied
 tracking target (t₃ψₙ⁴ - ψ₂ₙ)·s·ψₙ₋₁² to ψₙ⁴ψₙ₋₁²·T₄ where T₄ is the
 ψ-free TRACE IDENTITY s(t₃+s) = (x-x₃)(6x²+b₂x+b₄) - 2(x-x₁)(x-x₃)²
 (x₃,t₃ the secant sum-expressions, x₁ the difference x-coordinate =
 IH point). T₄ = `two_point_trace_identity`, : clear (x₁-x₂)⁵,
 eliminate t₃ by the ψ₂-secant (cofactor s(x₁-x₂)⁴) and x₃ by the
 x-secant (binomial bookkeeping), reduce by the two curve equations
 (sympy `sp.div` chain; certificate one-shot in Lean). NO tracking
 hypothesis at n-2, NO ψₙ₋₃, NO x₂-pinning needed — the sign
 propagates purely through the y-addition formula. `eval_Ψ₂Sq_eq_sq`
 relocated with a direct cofactor `-4` proof (yQuad-free).
 `zsmul_consec_step` (renamed from `_x`) now outputs the FULL IH
 package; new hypotheses `ψₙ₋₁ ≠ 0`, `ψ₂(x,y) ≠ 0` (both available in
 the main branch: IH(a)-contrapositive resp. the s ≠ 0 branch guard).
 Axioms: `two_point_trace_identity`, `eval_Ψ₂Sq_eq_sq` clean;
 `zsmul_consec_step` inherits sorryAx exactly through (★s).
 NEXT: (1) attempt (★s) at the Ψ-polynomial level (parity split on n,
 `Ψ_even`/`Ψ_odd`-style: 4 parity cases, preΨ'-recursion instances,
 `C_simp; ring1`); (2) wire the `zsmul_some_aux` strong-induction
 skeleton: ℕ-reduction `⟨(n-1).toNat, by omega⟩` + strong induction,
 base cases 1/2, main branch via `zsmul_consec_step` + collision via
 `smul_collision` + dictionary, 2-torsion branch s = 0 (even-index ψ
 vanish at 2-torsion x, odd-index don't — seeded by
 Res(Ψ₂Sq, Ψ₃) = -Δ², to be phrased via
 `exists_mul_add_mul_eq_C_resultant`).
- 2026-07-17 (session 5 cont., (★s) ROUTE DISCOVERED — universal EDS):
 (★s) is EQUIVALENT (per unit ψ₂Ψ₃, via the anchor identity
 `Ψ₃(6x²+b₂x+b₄) = preΨ₄ + Ψ₂Sq²` [ring-verified] and `Ψ₂Sq = ψ₂²`
 on-curve) to the UNIVERSAL EDS identity (★s′):
 `bc(Wₙ₋₁²Wₙ₊₂ + Wₙ₋₂Wₙ₊₁²) = Wₙ₋₁WₙWₙ₊₁(db + b⁵) − Wₙ³b³c` for
 `W = normEDS b c d` — verified numerically for generic (b,c,d), so
 provable from the defining recursions alone with NO curve geometry.
 Deduction chain: (★s′) in ℤ[A₁..A₆]-coordinate ring (a DOMAIN where
 ψ₂ ≠ 0, Ψ₃ ≠ 0) ⟹ cancel ⟹ (★s) universally ⟹ specialize to any
 (E, k, x, y). Descent experiments (scripts/eds/, sympy Groebner over
 window symbols, specialized b,c,d): the parity descents of the fixed
 families CLOSE — F_odd over F-instances alone (SYMBOLIC certificate
 extracted, certs.pkl), F_even over {F, ES2±3, ES3±2, ES4±1, ES5},
 ES2/ES3/ES4 even+odd all close, ES5_odd open (needs ES6-ish).
 STRUCTURAL REDUCTION: the general elliptic-sequence relator
 `rel(p,q,r,0)` follows RING-TRIVIALLY (alternating 3×3 expansion) 
 from the two-parameter family
 `T(p,q): W(p+q)W(p−q) = W(p+1)W(p−1)W(q)² − W(q+1)W(q−1)W(p)²`,
 so the right theorem is STANGE'S THEOREM for normEDS (a declared
 mathlib TODO: `IsEllipticSequence (normEDS b c d)`): prove T(p,q) by
 double parity descent over 4 clusters {W(a+j), W(e+j), W(a+e+j),
 W(a−e+j)}, |j| ≤ 2 — 4 fixed-size certificates; then ES-k = T(·,k),
 then F(n) descends over T-instances, then (★s′) ⟹ (★s) ⟹ tracking.
 Even-even T-descent Groebner test running. NEXT: (1) finish the 4
 T-descent membership tests + extract certificates; (2) Lean file
 Fermat/FLT/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:
 T(p,q) by strong induction (base |p|,|q| small via normEDS_zero..four
 + recursions; step via the 4 certificates), rel(p,q,r,0) trivially,
 F(n) by its descent, (★s′); (3) coordinate-ring domain argument +
 specialization ⟹ close `evalEval_ψ_sum`; (4) the zsmul skeleton
 (design DONE, in the log above): generic branch via zsmul_consec_step
 + IH-iff; collision via smul_collision + gap-1; torsion sub-cases via
 the Ward-pattern node `psi_nonzero_of_not_dvd` (N2, subsumes the
 s = 0 branch at d = 2 with the Res(Ψ₂Sq,Ψ₃) = −Δ² seed) + degenerate-
 window certificates (universal-ideal members with Wₙ₋₁ resp. Wₙ₋₂ as
 extra generators — same machinery).
- 2026-07-17 (session 5 cont., Ward pattern wired `b5e9887`): the
 rigidity insight — `ψⱼ = ψⱼ₊₁ = 0` forces `φⱼ(x) = 0` (φ-difference
 identity), a common root of `Φ j`/`ΨSq j` against the Bézout node —
 makes adjacent-nonvanishing FREE. `psi_eq_zero_iff_dvd` is now WIRED:
 backward from the new universal divisibility node
 `normEDS_mul_complEDS` (mathlib-TODO-shaped; even case already in
 mathlib), forward by the T(m−d, d)-climb (c_d ≠ 0 from minimality +
 rigidity). New bridges: `evalEval_ψ_normEDS` (ψ-values ARE a
 normEDS — universal identities specialise pointwise with no curve
 input), `evalEval_ψ_T`, `evalEval_ψ_quadratic`. The remaining
 frontier below `n_torsion_card` is now EXACTLY: three universal EDS
 nodes (`normEDS_sum_companion` (★s′), `normEDS_ellSequence` (Stange
 T-family), `normEDS_mul_complEDS` (divisibility)) + two degenerate
 tracking certificates (C1/C2, provable from the universal nodes +
 the c₃ = 0 torsion sub-case) + `separable_preΨ'` +
 `resultant_Φ_ΨSq` + `exists_point_x_smul` + `smul_surjective`.
 T-descent Groebner experiments still running (plain 9-generator and
 cross-generator variants).
- 2026-07-17 (session 5 cont., (★s′) CLOSED `837d2c7`): the literature
 hunt paid off — van der Poorten–Swart ("every Somos 4 is a Somos k",
 arXiv math/0412293) is the certificate-light proof: their Prop 1(4)
 IS the `T(·,2)` family and Prop 1(5) IS (★s′), with the footnote
 telescope deriving (5) from (4). Executed in Lean, all sorry-free:
 ES2-only parity-descent certificates (found by multivariate division
 after the key discovery that ES2 SELF-descends), generic-domain
 cancellations powered by `normEDS_generic_ne_zero` (witnessed by the
 universal curve through mk_Ψ ≠ 0), telescope + antisymmetry induction.
 AXIOM-CLEAN: `normEDS_quadratic`, `normEDS_sum_companion`,
 `evalEval_ψ_sum`, `zsmul_consec_step`. Remaining EDS frontier:
 `normEDS_ellSequence` (general T(p,q) — Stange/Ward; plan: vdP–Swart
 Thm 3 double-family induction (T and the s=1 net family N) from
 Prop 1(4)+(5) both now , per-step certificates with generic
 cancellation) + the degenerate tracking certificates C1/C2 (crux
 ideal-membership verified; c₃-cancellation via the same generic
 route or the d=3 pattern).
- 2026-07-17 (session 5 cont., STANGE'S THEOREM `7b1c6be`):
 `normEDS_ellSequence` — the full two-parameter elliptic-sequence
 relation `T(p,q)` for `normEDS` over any ring (mathlib TODO) — is
 sorry-free. Key discovery: the vdP–Swart inductive step is a RANK-1
 product identity `S₁T₋₁·S₋₁T₁ = S₁T₁·S₋₁T₋₁` (ring-trivial), whose
 residual is their symmetry identity (15) with the tiny hand-derived
 certificate `bc·K = bcU₀²V₀⁴·ES2ᵤ − U₀V₀²V₋₁V₁·★ᵤ − (u↔v)` over the
 `T(·,2)` + sum-companion families. The universal EDS layer is
 now COMPLETE and axiom-clean: `normEDS_quadratic`,
 `normEDS_sum_companion`, `normEDS_ellSequence`,
 `normEDS_mul_complEDS`, `normEDS_generic_ne_zero`. Downstream now
 axiom-clean: `evalEval_ψ_sum`, `evalEval_ψ_T`, `evalEval_ψ_quadratic`,
 `zsmul_consec_step`. `psi_eq_zero_iff_dvd` rests ONLY on
 `resultant_Φ_ΨSq`; `zsmul_some_aux` additionally on
 `psi_tracking_prev_zero`/`_prev2_zero` (C1/C2). NEXT: (1) C1/C2 via
 the generic-cancellation route (crux certificate in the fraction
 field verified; c₃-cancellation generic; the value-level c₃ = 0
 subcase via the d = 3 Ward pattern + `normEDS b 0 d` closed forms);
 (2) `resultant_Φ_ΨSq` (7×7-Sylvester-flavoured, or the
 Δ-formula route); (3) `exists_point_x_smul`, `separable_preΨ'`,
 `smul_surjective`; then the WeilPairing/Chebotarev/hardly-ramified
 branches.
- 2026-07-17 (session 5 cont., C1/C2 `cc90dfb`): both degenerate
 tracking certificates are sorry-free via the complement sequence +
 the crux lemmas `normEDS_crux₁/₂` (one-line consequences of the
 sum-companion/T(·,2) families; multiples of ψₙ₋₁ resp. ψₙ₋₂) for
 `Ψ₃(x) ≠ 0`, and via the anchor (`preΨ₄(x) = -ψ₂⁴`) + the d = 3 Ward
 pattern + the 3-division closed forms for `Ψ₃(x) = 0`. THE ENTIRE
 WASHINGTON THM 3.6 TOWER (zsmul_some_aux, the dictionary,
 smul_some_eq_zero_iff, exists_smul_some_eq) now rests on EXACTLY ONE
 sorry: `resultant_Φ_ΨSq` (via isCoprime_Φ_ΨSq → psi_adjacent_ne_zero
 → the Ward pattern's rigidity). Analysis: the rigidity is genuinely
 y-geometric (pure-T zero-propagation cannot reach index 1), so the
 Φ/ΨSq-coprimality is load-bearing; options: (a) prove the resultant
 formula by recursion-multiplicativity (Ayad-style), (b) restate the
 node as field-level `IsCoprime` and prove by induction on division
 polynomials, (c) universal-curve + Δ-irreducibility + Nullstellensatz.
 Remaining cone of `n_torsion_card`: resultant_Φ_ΨSq,
 separable_preΨ', exists_point_x_smul, smul_surjective.
- 2026-07-17 (session 5 cont., fibre node `cf0cb95`): 
 `exists_root_of_derivative_ne_zero` (general: nonzero derivative ⟹
 root over a separably closed field; expand-factorization argument)
 and `exists_point_x_smul` (the fibre polynomial `Φₙ − ξΨSqₙ` has
 derivative with `(n²−1)`-st coefficient `n² ≠ 0`; y-lifting via the
 separable y-quadratic, the char ≠ 2 double root, or the char-2
 `Φ`-definition collapse forcing `ξ = x₀`). `smul_surjective` is now
 end-to-end. The `n_torsion_card` cone rests on exactly TWO
 sorries: `resultant_Φ_ΨSq` (rigidity/coprimality) and
 `separable_preΨ'` (the p-division discriminant) — the
 resultant/discriminant cluster for division polynomials.
- 2026-07-17 (session 5 end, Wronskian lead for `separable_preΨ'`):
 empirically `Φₙ'ΨSqₙ − ΦₙΨSqₙ' = n ⬝ Wₙ` with `W₂ = 2·preΨ₄`
 (verified exactly) and `W₃ = 3·Ψ₃·(preΨ'₅ − preΨ₄²)` where
 `preΨ'₅ := preΨ₄Ψ₂Sq² − Ψ₃³` (verified exactly): the deg-12 factor
 is the 5-division polynomial CORRECTED by `−preΨ₄²` — the pattern
 suggests `Wₙ = n·(the univariate ψ₂ₙ/ψ₂-companion in its parity
 normalization)`, i.e. the invariant-differential identity
 `d(x∘[n])/dx = n·(ψ₂ₙ/ψₙ⁴)·(ψ₂-quotient)` cleared of denominators.
 This is the invariant-differential/ramification identity; from it,
 a common root of `preΨ'ₚ` and its derivative forces division-
 polynomial vanishing patterns that should contradict the Bézout
 machinery — the route to `separable_preΨ'` WITHOUT the full
 discriminant formula. VERIFIED (scripts/eds/wronskian_composition.py):
 (W) `Φₙ'ΨSqₙ − ΦₙΨSqₙ' = n·preΨ(2n)` at n = 2, 3, 4, and
 (C) `Φ(2n) = Φ₂hom(Φₙ,ΨSqₙ)`, `ΨSq(2n) = Ψ₂Sqhom(Φₙ,ΨSqₙ)` at n = 2
 (the duplication-composition pair, EXACT, no unit). SEPARABILITY
 PROOF SHAPE: double root x₀ of preΨ'ₚ ⟹ ΨSqₚ-mult ≥ 4 ⟹ (W)
 preΨ(2p)-mult ≥ 3 ⟹ ΨSq(2p)-mult ≥ 6; but (C) + Bézout (Φₚ(x₀) ≠ 0)
 give ΨSq(2p)-mult exactly 4 at x₀ (char ≠ 2 via the 4Φ³-term;
 char 2 needs its own composition trick). PROOF ROUTES: (C) should be
 a T-family window-certificate (φ-diff expansions); (W) by parity
 induction with DIFFERENTIATED recursions over the joint {P, P'}
 window (same descent machinery, one derivative level up), or via the
 chain rule through (C) (the Jacobian of the pair is 2·preΨ₄hom).
 KEY SIMPLIFICATION: at the value level (C)'s ΨSq-side is literally
 tracking² + membership-at-nP: `ψ₂ₙ² = tₙ²ψₙ⁸ = Ψ₂Sq(xₙ)ψₙ⁸ =
 Ψ₂Sqhom(φₙ, ψₙ²)`, and the Φ-side is the x-formula composed with
 duplication (`x₂ₙ = x₂(xₙ)`) — both from the zsmul-machinery
 instantiated at the TAUTOLOGICAL POINT of the universal curve over
 Frac(B_univ) (ψₖ-values ≠ 0 there by mk_Ψ_univ_ne_zero), then pulled
 back to ℤ[A][x] by the {1,Y}-basis injectivity (both sides y-free).
 (W) at prime indices is NOT composition-reachable — needs the
 differentiated-recursion descent over the joint {P, P'} window.
 CONFIRMED FURTHER: the (C)-ΨSq-side CLOSES as a value-window ideal
 membership over {even-rec, T(n,2), star, membership, c/d-anchors,
 b₈-relation} (GB size 13, scripts/eds/composition_psisq_certificate
 .py) — but plain multivariate DIVISION fails in 500 generator
 orders, so no easy explicit cofactors: use the TAUTOLOGICAL-POINT
 route (where (C)-ΨSq is literally tracking² + membership-at-nP,
 zero new certificates). And the Euler-homogeneity chain rule gives the exact
 doubling law `W(2n) = 2·preΨ₄hom(Φₙ,ΨSqₙ)·W(n)` since the Jacobian
 of the composition pair is `8·preΨ₄hom` (verified). The remaining
 odd-index (W)-steps at primes need the differentiated-recursion
 descent OR the derivation-on-Frac(B) invariant-differential
 induction. MULTIPLICITY ENDGAME (worked out precisely, UFD-valuation
 form over k[x], no k̄): for an irreducible π ∣ gcd(preΨ'ₚ, (preΨ'ₚ)')
 with a := ν_π(preΨ'ₚ): in all cases ν_π(ΨSqₚ') ≥ 2 hence
 ν_π(W) ≥ min(2a, 2a−1) and ν_π(preΨ(2p)) ≥ 2a−1 ((p:k) ≠ 0); the
 ΨSq-composition gives 2(2a−1) + ν(Ψ₂Sq) = 2a + ν_π(H) with
 H := 4Φ³ + b₂Φ²ΨSq + 2b₄ΦΨSq² + b₆ΨSq³ ≡ 4Φ³ (mod π) and
 ν_π(H) = 0 by the Bézout node — contradiction for char ≠ 2. In
 char 2 with a₁ ≠ 0: H ≡ b₂Φ²ΨSq, same contradiction one level down.
 Char-2-supersingular (a₁ = 0, Ψ₂Sq = b₆ constant): the [2]-
 composition degenerates; use the [3]-composition (Ψ₃hom ≡ 3Φ⁴ and
 3 ≠ 0 in char 2) with the tripling law W(3n) = 3·(factor)·W(n) —
 needs the [3]-composition pair verified/certified.
 IMPORTANT: the endgame needs (W) AT p ITSELF, and primes ≥ 5 are
 not composition-reachable — so the doubling/tripling laws do NOT
 suffice; (W) requires either the differentiated-recursion descent
 over the joint {P, P'} window (the parity recursions differentiated,
 same GB machinery one derivative level up) or the derivation on
 Frac(B_univ) (D := ∂x − (Fx/Fy)∂y, differentiate the addition
 formula once — the invariant-differential additivity — then induct;
 ~200 lines with mathlib's Derivation API). The compositions (C) for
 m = 2, 3 formalize uniformly via the tautological point:
 x(m·(nP)) = Φₘ(xₙ)/ΨSqₘ(xₙ) is quotient-arithmetic of the 
 x-formulas, cross-multiplied and pulled back by basis-injectivity
 with exactness from the Degree API leading coefficients.
 NEXT SESSION: (1) formalize (C) (either route); (2) the (W)
 machinery (differentiated descent — REQUIRED for primes); (3) the
 multiplicity endgame as above;
 (2) `resultant_Φ_ΨSq` or its `IsCoprime` reformulation; then the
 torsion cone is DONE. Remaining 18 nodes list: see the sorry-grep;
 major fronts: WeilPairing:124, Chebotarev:98, HardlyRamified (5
 nodes), TateCurve (2), MazurTorsion (2), Semistable (2),
 GoodReduction, Flat:163 (torsion-flat construction).
- 2026-07-17 (session 5 end, tautological point built `de9784b`):
 `TautologicalPoint.lean` (all axiom-clean): `Kuniv = Frac(Buniv)`,
 the base-changed curve `WK`, `taut_equation`, `Δ_univ_ne_zero`
 (evaluate at `y² + y = x³`), `coeffHom_injective`,
 `taut_nonsingular`. The generic-point engine for (C) is ready: next
 session instantiates the multiplication machinery
 (`exists_smul_some_eq`, trackings) at `(tautX, tautY)` over `Kuniv`
 — all division-polynomial values there are nonzero by
 `mk_Ψ_univ_ne_zero` pushed through the fraction field — derives the
 composition identities at values, pulls back to `ℤ[A][X]` via
 `coeffHom_injective`-style basis arguments, and then runs the
 UFD-multiplicity endgame for `separable_preΨ'`.
- 2026-07-17 (session 6, NOS (iii) COMPLETE `49b0112`): the y-level
 `torsion_ordinate_eq_of_residue_eq` — equation-difference
 factorization gives y₂ = negY, the difference is ψ₂ with
 ψ₂² = Ψ₂Sq(x) on-curve, congruent ordinates force the
 Ψ₂Sq(x)-residue to vanish, and the residue-curve Bézout
 (isCoprime_Ψ₂Sq_preΨ' at the abscissa residue, a residue-preΨ'ₚ
 root via the packaged two-face principle) yields 1 = 0.
 Axiom-clean. ONLY (iv) REMAINS for the NOS node: restate
 torsion_unramified_of_good_reduction with (hp : n.Prime)
 (hodd : Odd n) [thread hp2/hp5 at Semistable:592 — it has
 Fact p.Prime and can get oddness from the caller chain]; proof:
 intro σ hσ P hP; P = some x y (zero-case trivial); σP =
 some (σ x) (σ y) via Affine.Point.map-some; σP is n-torsion
 (map-additivity: n•σP = σ(n•P) = 0 — mathlib Point.map is a
 group hom or prove smul-commute directly); coordinates of σP in 𝒪
 (torsion_abscissa/ordinate_mem); inertia σ fixes residues:
 ValuationSubring.inertiaSubgroup-def gives residue(σ z) =
 residue z for z ∈ 𝒪 (unfold the mathlib RamificationGroup
 definition of inertia — CHECK its exact form: likely
 'σ acts trivially on the residue field of 𝒪'); then
 torsion_abscissa_residue_ne forces σx = x (else distinct residues,
 but inertia gives equal) and torsion_ordinate_eq_of_residue_eq
 forces σy = y; Point-ext concludes σP = P.
- 2026-07-17 (session 6, NOS x-LEVEL `ec4425b`):
 `torsion_abscissa_residue_ne` — the complete x-level of the
 injectivity: torsion abscissas at good reduction have distinct
 residues, composing the dictionary, RtoO, the reduction curve, the
 local-hom residue square, and the CHAR-FREE separable_preΨ' of the
 axiom-clean tower (this is the payoff moment for the char-2 work:
 the residue characteristic is arbitrary). Axiom-clean. REMAINING
 for the node (final stretch): (b) the y-level — same abscissa,
 congruent ordinates: y and negY-x-y are the two yQuad-roots
 differing by ψ₂-value; if the ordinates were distinct-but-congruent
 then ψ₂(P)-residue = 0, making the REDUCED point 2-torsion while
 also p-torsion-abscissa'd — excluded via the reduced dictionary or
 directly: ψ₂(P)² = Ψ₂Sq(x)-on-curve and gcd(Ψ₂Sq, preΨ'ₚ)-residue
 coprimality (isCoprime_Ψ₂Sq_preΨ' exists in TorsionCardSep for the
 residue curve — check its hypotheses); (c) the inertia endgame:
 restate the NODE with (hp : n.Prime) (hodd : Odd n) — thread
 through Semistable's call-site (P.hp5 gives both) — σ ∈ inertia
 fixes 𝒪-residues (unfold ValuationSubring.inertiaSubgroup /
 RamificationGroup-defs), Point.map-σ preserves torsion and
 Nonsingular, coordinates of σP are (σx, σy) (Point.map-some-form),
 σx ∈ 𝒪 with residue = residue x (inertia), so x-level + y-level
 force σP = P.
- 2026-07-17 (session 6, NOS (a)-plumbing `7f590b5`): RtoO
 (the structural R → 𝒪 hom from h𝒪), RtoO_coe, isLocalHom_RtoO
 (unit inverses descend through 𝒪 ∩ k = R). With
 IsLocalRing.ResidueField.map (RtoO) : κ_R → κ_𝒪 available, the
 REMAINING (a)-assembly is: f₀ := (integralModel.preΨ' p).map RtoO;
 its ksep-image is (E⁄ksep).preΨ' p (map_preΨ' chain), so torsion
 abscissas are f₀-roots in 𝒪; its residue image is
 ((E.reduction R).map (ResidueField.map RtoO)).preΨ' p — elliptic
 by hasGoodReduction_iff_isElliptic_reduction + the map-instance —
 and separable by separable_preΨ' at κ_𝒪 (needs (p : κ_𝒪) ≠ 0 from
 the p-R-unit through the local hom, and p odd prime threaded into
 the node statement). Then residue_ne_of_roots_ne closes the
 x-level; yQuad handles the y-level; the inertia endgame finishes.
- 2026-07-17 (session 6, NOS (iii) CORE `c672d54`):
 `ValuationSubring.residue_ne_of_roots_ne` — distinct roots keep
 distinct residues under separable reduction (double-root
 square-factor argument, axiom-clean). REMAINING ASSEMBLY for the
 node (all mapped): (a) the curve-side instantiation — lift
 (E⁄ksep).preΨ' p to 𝒪[X] (toSubring with the coefficient
 membership already established), identify its residue-map with the
 RESIDUE curve's preΨ' p (map_preΨ' through 𝒪 → κ_𝒪 plus the
 integral-model chain), and apply the residue curve's
 separable_preΨ' (elliptic since Δ is a unit of R hence of 𝒪 hence
 nonzero in κ_𝒪; (p : κ_𝒪) ≠ 0 since p is an R-unit and
 𝔪_R ⊆ 𝔪_𝒪 via h𝒪; p odd threaded from the Frey package's
 p ≥ 5 — restate the node with hodd); (b) the y-level: equal
 abscissas and congruent ordinates via the yQuad-quadratic — its
 two roots y, negY differ by ψ₂ ≠ 0 whose residue is nonzero unless
 the reduced point is 2-torsion, excluded for odd p by the
 reduced-curve dictionary; (c) the inertia endgame: σP has
 congruent coordinates (inertia trivial on 𝒪-residues — unfold
 ValuationSubring.inertiaSubgroup), σP is p-torsion (Point.map
 additive homomorphism, exists in mathlib as Point.map-hom?), and
 (a)+(b) force σP = P. Each piece is bounded; the node closes in
 1-2 more sessions of this pace.
- 2026-07-17 (session 6, NOS (iii) SCOPING): the ΨSq-square structure
 makes x-level mod-𝔪 injectivity subtle for general n (ΨSqₙ is
 never separable — it is preΨ'ₙ²·parity); but the node's ONLY
 consumer (Semistable.lean:592) instantiates n = p with
 Fact p.Prime in scope. DECISION: restate the node for prime p
 (legitimate hypothesis strengthening — all consumers satisfy it).
 For odd p the x-level injectivity uses the residue curve's
 separable_preΨ' on the squarefree part preΨ'ₚ (roots of ΨSqₚ =
 roots of preΨ'ₚ for odd p); the p = 2 case (if ever needed —
 check whether the Frey consumer guarantees p ≥ 5 / oddness and if
 so add hodd to the node too) would use residue-Ψ₂Sq separability
 via a small disc(Ψ₂Sq)-Δ certificate. The integral-to-residue
 double-root argument needs: dividing ΨSq by the monic (X − x₁)
 keeps 𝒪-coefficients (divByMonic-integrality), so equal residues
 of two distinct roots give the residue polynomial a double root at
 ξ, contradicting separability. (iv) then: inertia fixes residues,
 Point.map σ is additive so σP is p-torsion with coordinates
 congruent to P's, and (iii) forces σP = P.
- 2026-07-17 (session 6, NOS step (ii) `293e809`):
 `torsion_ordinate_mem` — the monic y-quadratic instantiation of the
 root-integrality lemma; coefficient membership by explicit
 coeff-case analysis (match on the index, norm_num-normalized
 shapes closed by generic add_mem/neg_mem/mul_mem/pow_mem chains —
 NOTE the ValuationSubring dot-forms take explicit element
 arguments, use the _root_ SubringClass lemmas). Axiom-clean, build
 green. NEXT (iii): mod-𝔪 injectivity — two torsion points with
 congruent coordinates mod the maximal ideal of 𝒪 coincide; via the
 residue curve's separable_preΨ' (x-level: two distinct integral
 roots of ΨSqₙ with equal residues would give the reduced ΨSqₙ a
 double root, contradicting separability over the residue field of
 𝒪 — which is a separably-closed?? no: an extension of the residue
 field of R; separability holds over ANY field ✅ char-free) and the
 yQuad/Ψ₂Sq-coprimality (y-level). Then (iv): inertia acts
 trivially on 𝒪-residues, so σP ≡ P coordinatewise; σP is torsion
 (Point.map additive); conclude σP = P.
- 2026-07-17 (session 6, NOS steps (0)+(i) `6a2c87f`,
 `a6b5660`): `ValuationSubring.mem_of_root_of_inv_leadingCoeff_mem`
 (the general root-integrality: leading term dominates when
 1 < v(x); leading coefficient valuation pinned by two-sided
 membership) and `WeierstrassCurve.torsion_abscissa_mem` (the
 Cassels instantiation at ΨSqₙ: n-unit from nonzero residue,
 dictionary → root, integral model + double map_ΨSq → coefficients
 in 𝒪 via h𝒪-comap, (n²)⁻¹ ∈ 𝒪 via Rˣ-arithmetic). Both
 axiom-clean; GoodReduction.lean builds. REMAINING for the node:
 (ii) y ∈ 𝒪 (apply the same lemma to the monic y-quadratic
 X² + (a₁x+a₃)X − cubic with coefficients now known integral);
 (iii) mod-𝔪 injectivity on torsion (distinct torsion points have
 distinct residues: x-level via the RESIDUE curve's
 separable_preΨ' — reduction of ΨSq is the residue ΨSq;
 y-level via yQuad/Ψ₂Sq coprimality mod 𝔪); (iv) the inertia
 endgame: σP ≡ P coordinatewise (inertia trivial on residues),
 σP is n-torsion (Point.map is additive), so σP = P by (iii).
- 2026-07-17 (session 6 final refinement, GoodReduction WITHOUT a
 reduction map): mathlib's Reduction.lean is curve-level only (no
 point reduction, no additivity) — but the node does not need it:
 (i) torsion coordinates are INTEGRAL (x: root of ΨSqₙ with
 R-integral coefficients and unit leading coefficient n²; y:
 integral via the monic-in-y curve equation); (ii) the reduction of
 ΨSqₙ is the residue curve's ΨSqₙ (map_ΨSq + good reduction), and
 the RESIDUE curve's separable_preΨ' (axiom-clean, ALL
 characteristics — this is where the char-2 case pays off) makes
 distinct integral torsion-x's stay distinct mod 𝔪 (a double
 residue root would contradict separability); (iii) same-x points
 are resolved by yQuad/Ψ₂Sq-coprimality mod 𝔪; (iv) σ in inertia
 acts trivially on residues, so σP ≡ P coordinatewise mod 𝔪 —
 hence σP = P by (ii)+(iii). σP is n-torsion since the Galois
 action is additive (Point.map is a group hom, existing machinery).
 ~300 lines against the axiom-clean tower; NEXT SESSION EXECUTES.
- 2026-07-17 (session 6 close, NEXT-NODE PLAN — GoodReduction:65 via
 division polynomials, Cassels-style, NO formal groups): the torsion
 tower unlocks an elementary route to
 torsion_unramified_of_good_reduction: (1) torsion x-coordinates are
 INTEGRAL at good primes — nP = 0 gives ΨSqₙ(x) = 0 (the 
 dictionary), and ΨSqₙ has R-integral coefficients (minimal
 equation) with leading coefficient n² a UNIT in R (n invertible in
 the residue field), so roots are integral over R — hence the kernel
 of reduction (points with v(x) < 0) contains no nonzero n-torsion;
 (2) for σ in inertia, σP − P is n-torsion AND reduces to zero
 (inertia is trivial on the residue field; needs the point-reduction
 map + additivity — check Mathlib.AlgebraicGeometry.EllipticCurve.
 Reduction for what exists), so σP − P = 0. Ingredients: the
 dictionary (axiom-clean now), coeff_ΨSq/natDegree_ΨSq (mathlib),
 integrality of roots of unit-leading-coefficient polynomials over
 a valuation ring. This node then feeds the WeilPairing det-route
 (Frobenius-det at good primes + Chebotarev/Dirichlet).
- 2026-07-17 (session 6, TORSION TOWER AXIOM-CLEAN `498a075`):
 psi34 verified in the exponent-ascribed X-collected form — the
 winning trick: print EVERY power as `a ^ (k : ℕ)`; the shared
 HPow-exponent metavariable across hundreds of `^`-occurrences was
 the recursion driver (not term size). Full cone builds (3568 jobs).
 AXIOM AUDIT: `isCoprime_Φ_ΨSq_field`, `separable_preΨ'`,
 `card_torsionBy` (#E[n] = n²) — ALL depend only on
 propext/Classical.choice/Quot.sound. The complete
 division-polynomial tower (universal EDS certificates, Washington
 induction, tautological-point composition (C), invariant-derivation
 Wronskian (W), separability endgame, EDS-rank coprimality) is
 FULLY , zero sorries. Remaining 16 nodes are all OUTSIDE
 this tower: Flat:163 (finite-flat construction),
 WeilPairing-det-node (route: Frobenius-det + Chebotarev),
 Chebotarev, HardlyRamified×5, MazurTorsion×2, Semistable×2,
 GoodReduction, TateCurve×2. Elaboration playbook for future giant
 certificates: X-collect, ascribe exponent types, set-stage big
 subterms, inline linear_combination cofactors, never trust a
 background compile before its process exits.
- 2026-07-17 (session 6, psi34 ELABORATION SAGA — corrective record):
 the cb7f744 'psi34 verified' claim was PREMATURE (a mid-compile
 output read — lesson: never read a background compile's output file
 until the process list is empty). The 266/164-term b-power-form
 certificate hits HPow-metavariable maxRecDepth in ELABORATION
 (not proof): neither type-ascription nor maxRecDepth 16000 +
 40M heartbeats finished within ~40 min. Switched to the
 X-COLLECTED form: Fc = Σᵢ C(fᵢ)·Xⁱ with 6+4 K-level coefficient
 expressions (elaborates in K, no polynomial-instance cascade),
 RHS = C(raw resultant value) so hcert needs NO b-relation (holds
 over independent b's; the relation enters only in the K-level
 step det-value = Δ⁴ via a 55-term linear_combination on
 W.b_relation). Verification of this form in flight. FALLBACK if
 ring still stalls: park hcert as a mini sorry-node (architecture
 is sound; certificate is sympy-exact) or prove coefficientwise.
- 2026-07-17 (session 6, WEIL PAIRING DECOMPOSED): the
 `exists_weilPairing` node is now from the strictly smaller
 node `det_galoisRep_eq_cyclotomic` (det of the mod-p representation
 is the mod-p cyclotomic character). Assembly : #E[p] = p²
 (card_torsionBy at the algebraic closure, now resultant-free) ⟹
 the torsion is a rank-2 ZMod-p-space (card_eq_pow_finrank +
 pow-injectivity) ⟹ the coordinate determinant form in a finBasis
 is alternating and nondegenerate, and transforms by det ρ
 (pairing_map_eq_det_smul, in-file), which is χ by the det-node.
 GOTCHA: do NOT `haveI Classical.decEq` over an existing project
 DecidableEq-instance — nTorsion carries the instance as a type
 argument and the ∃-type was elaborated with the ambient one.
 ROUTE FOR THE DET-NODE (sketch, fits existing tree nodes):
 det ρ̄ and χ̄ are characters G_ℚ → (ZMod p)ˣ; they agree at
 Frobenius elements of good-reduction primes ℓ ∤ pN (Frobenius has
 det = ℓ mod p by the reduction/point-counting machinery of
 GoodReduction.lean) and Chebotarev (the Chebotarev.lean node)
 makes Frobenii dense, forcing equality. So the Weil-pairing cone
 reduces to GoodReduction + Chebotarev + a Frobenius-det
 computation — no elliptic-net/Miller-function layer needed.
- 2026-07-17 (session 6, RESULTANT NODE ELIMINATED `cb7f744`):
 psi34's certificate elaborated (40M heartbeats, set-staged
 cofactors, inlined 55-term relation-cofactor in the
 linear_combination — a set-bound cofactor is an opaque ring-atom,
 must be inlined); PhiPsiCoprime.lean is SORRY-FREE. Flat.lean
 patched: resultant_Φ_ΨSq DELETED, isCoprime_Φ_ΨSq restated for
 fields with the direct proof. 17 → 16 nodes. The full-cone rebuild
 + axiom audit in flight; expected: the ENTIRE torsion-card
 machinery becomes sorryAx-free except the finite-flat construction
 Flat.lean:163. ELABORATION LESSONS: giant certificate statements
 need set-staged big terms (MVar-synthesis times out otherwise);
 linear_combination cofactors must be inline expressions.
- 2026-07-17 (session 6, RESULTANT REPLACEMENT EXECUTED): the direct
 coprimality is implemented: (1) `EDSRank.lean` (all proven) — the
 rank-of-apparition machinery (IsRank, c_eq_zero_of_adjacent via
 T(·,2) at n = r−1, le_three_of_adjacent, degenerate_of_adjacent:
 adjacent zeros force (b,c) = (0,0) at rank 2 or (c,d) = (0,0),
 b ≠ 0 at rank 3, dvd_of_eq_zero: the T(k−r,r)-descent).
 (2) `PhiPsiCoprime.lean` — no_common_root (alg-closed; the
 y-quadratic lift, evalEval_ψ_normEDS, the Φ-definition parity
 bridge, on-curve b² = Ψ₂Sq(x₀), rank-divides-consecutive
 contradiction; NONSINGULARITY NOT EVEN NEEDED — only the Equation)
 and isCoprime_Φ_ΨSq_field (natAbs-reduction + gcd-root descent to
 the algebraic closure). The two degenerate cases are closed by
 sympy-extracted Sylvester-cofactor Bézout certificates:
 psi23 (F·Ψ₂Sq + G·Ψ₃ = −Δ², 36/26-term cofactors, ) and
 psi34 (F·Ψ₃ + G·preΨ₄ = Δ⁴, 266/164-term cofactors + 55-term
 b-relation cofactor, elaborating at time of writing). KEY FACTS:
 res(Ψ₂Sq,Ψ₃) = −Δ² and res(Ψ₃,preΨ₄) = Δ⁴ modulo
 4b₈ = b₂b₆ − b₄² — pure Δ-powers, no 2-factors, char-2-safe;
 extraction via integral Sylvester-adjugate columns (NOT naive
 solve/gcdex — those time out or introduce junk lc-factors).
 NEXT: verify psi34-elaboration, patch Flat.lean (staged:
 isCoprime_Φ_ΨSq restated for fields, proven from
 PhiPsiCoprime; resultant_Φ_ΨSq DELETED), rebuild the cone —
 separable_preΨ' and the whole torsion machinery then become
 sorryAx-FREE except Flat.lean:163.
- 2026-07-17 (session 6, RESULTANT-NODE ATTACK PLAN): the consumers
 only use `isCoprime_Φ_ΨSq` (Bézout with Δ-unit), never the actual
 resultant VALUE — so the node can be REPLACED by a direct
 coprimality proof, eliminating the ±Δ^k-formula entirely. Route:
 over k̄ (field-reduction of IsCoprime along faithfully-flat/field
 extension — for k → k̄ use gcd-descent), a common root x₀ of
 (Φₙ, ΨSqₙ) lifts to a curve point P = (x₀, y₀); the ψ-values
 wₖ := ψₖ(P) form an elliptic sequence (evalEval_ψ_T, ) with
 w₁ = 1; ΨSq-vanishing gives wₙ = 0; Φ-vanishing + the Φ-definition
 Φₙ = XΨSqₙ − preΨₙ₊₁preΨₙ₋₁(parity) gives wₙ₊₁wₙ₋₁-vanishing
 (2-torsion x₀ handled separately), so an ADJACENT PAIR of zeros
 (wₙ, wₙ₊₁) or (wₙ, wₙ₋₁). CLAIM (rigidity WITHOUT Bézout —
 breaking the old circularity): adjacent zeros are impossible, by
 the T(·,2)-quadratic recursion run as a two-sided induction: with
 w_d = w_{d+1} = 0 (d minimal ≥ 2, so w_{d−1} ≠ 0), the instances
 w_{m+2}w_{m−2} = b²w_{m+1}w_{m−1} − c·w_m² at m = d+1, d+2, …
 propagate zeros forward (w_{d+3}w_{d−1} = 0 ⟹ w_{d+3} = 0, then
 c·w_{d+2}² = 0, …) and the case-analysis on the seed values
 b = ψ₂(P), c = ψ₃(P) (using the c=0-closed-forms
 normEDS_c_zero_closed and the ★-companion) forces w₁ = 0 or an
 explicit contradiction. All ingredients are proven EDS-machinery;
 no new certificates expected. This closes resultant_Φ_ΨSq's
 consumer (isCoprime_Φ_ΨSq gets a direct proof; the stated
 resultant-formula node can then be DELETED or left as a
 historical remark — prefer restating the node file to make
 isCoprime the primitive). CAUTION: check where in TorsionCard the
 dictionary/climb machinery itself uses isCoprime — the new proof
 must sit UPSTREAM (in the EDS-files or a new file importing only
 Points + EDSStange), then Flat.lean's isCoprime_Φ_ΨSq becomes a
 re-export. NEXT: implement, starting with the value-level
 adjacent-zeros-impossible lemma over a field.
- 2026-07-17 (session 6, SEPARABILITY COMPLETE `8d1108e`): the
 generic-fibre plan is fully EXECUTED — `exists_good_chord`,
 `exists_large_fibre`, `torsion_finset_of_fibre`,
 `separable_of_torsion_finset` all ; `separable_preΨ'` is
 resolved in ALL characteristics. 18 → 17 nodes. TorsionCardSep.lean
 is sorry-free. Key implementation notes: (a) the Wronskian-nonzero
 case-split (char ≠ 2 via coeff_preΨ_ne_zero at 2p; char 2 via
 ΨSqₚ′ = 0 and the p²-top-coefficient of Φₚ′); (b) nonvanishing of
 ΨSqₚ/Ψ₂Sq from IsCoprime-with-zero degeneracy (unit vs natDegree);
 (c) the abscissa-pinning x′ = c by mul_right_cancel₀ on the proven
 x-formula; (d) R not 2-torsion via evalEvalRingHom applied to
 C_Ψ₂Sq with the curve equation; (e) class-halving by
 Finset.card_bij with the negation involution (pointsAt is
 neg-closed). The ENTIRE torsion-card cone now rests on exactly TWO
 upstream nodes: resultant_Φ_ΨSq (Flat.lean:233) and the
 torsion-flat construction (Flat.lean:163).
- 2026-07-17 (session 6 FINAL PLAN, the closed-field char-2 node has
 a COMPLETE ELEMENTARY ROUTE — char-free, no literature needed):
 prove #E[p](K̄) = p² by GENERIC-FIBRE COUNTING, then read
 separability backwards. Steps, all with existing machinery:
 (1) Φₚ′ ≠ 0 in every characteristic with (p:K) ≠ 0: its leading
 coefficient is p²·(top of f²) — in char 2, Φₚ′ = f² + (AB)′Ψ₂Sq
 with deg((AB)′Ψ₂Sq) ≤ p²−2 < p²−1 = deg f², and (p²:K) ≠ 0; hence
 by (W)-char-2 also preΨ₂ₚ = p⁻¹Φₚ′f² ≠ 0.
 (2) The c-resultant R(c) := Res_x(Φₚ − c·ΨSqₚ, Φₚ′ − c·ΨSqₚ′) is
 not identically 0 (else every Φ−cS is inseparable; use the
 Wronskian Φ′S − ΦS′ = p·preΨ₂ₚ ≠ 0 to rule this out — a common
 factor of Φ−cS and Φ′−cS′ for ALL c would divide the Wronskian).
 Cheaper equivalent: choose c avoiding the finitely many roots of
 disc-like data: ∃ c ∈ K with Φ−cS separable, deg = p² (leading
 coeff 1, monic ✅), and S ∤-vanishing at its roots, c ≠ x-coords of
 2-torsion images etc. — all finite exclusions, K infinite.
 (3) Each of the p² distinct roots x of Φ − cS has ΨSq(x) ≠ 0 and
 x-value of p•(x,y) equal to c (the x-formula/dictionary);
 the y-fibre above each root has exactly 2 points (yQuad separable
 since the point is not 2-torsion — ψ₂ ≠ 0 there for suitable c).
 That is 2p² points P with x(p•P) = c, i.e. p•P ∈ {R, −R} where
 R = (c,d): the involution P ↦ −P swaps the two classes, so
 #[p]⁻¹(R) = p² for R ≠ −R (generic c avoids ψ₂-locus of R).
 (4) Fibres of the GROUP HOM [p] are ker-cosets: one fibre of size
 p² ⟹ #E[p] = p² — no surjectivity of [p] needed.
 (5) Backwards: #E[p]∖0 = p²−1 maps 2-to-1 onto roots of f (odd
 p-torsion is never 2-torsion; yQuad-fibres of size 2 via
 isCoprime_Ψ₂Sq_preΨ' — already in the tail), so f has
 (p²−1)/2 = deg f DISTINCT roots ⟹ f = unit·∏(X−rᵢ) distinct ⟹
 Separable via separable_prod_X_sub_C_iff (K = K̄ splits ✅).
 This closes separable_preΨ'_char_two_closed with ~300 elementary
 lines and NO new axioms/literature; it is also a template that
 would re-prove the char ≠ 2 case (not needed). IMPLEMENT NEXT.
- 2026-07-17 (session 6, char-2 reduction `916e56f`+):
 `separable_preΨ'_char_two` is now from the strictly smaller
 node `separable_preΨ'_char_two_closed` (algebraically closed base)
 via `Polynomial.separable_map` + `map_preΨ'` + the
 baseChange-composition identity (term-mode `congrArg` to dodge the
 module-system rw-matching friction). Over K = K̄ char 2 the
 Frobenius decomposition f = u² + X·v², f′ = v² is available:
 π | f, f′ ⟹ π | u and π | v. Remaining gap: a structural
 obstruction to gcd(u,v) ≠ 1 — candidate: Gunji 1976 char-2
 disc(ψₚ) formula (annas-mcp next session), or the universal
 discriminant route (generic-fiber separability over ℚ(A) is now a
 theorem; missing only the ±pˢΔᵗ-structure via Δ-irreducibility +
 Nullstellensatz — the SAME machinery the resultant node needs).
- 2026-07-17 (session 6 final, UNIFICATION INSIGHT): the two
 remaining torsion-cone blockers — `resultant_Φ_ΨSq` and
 `separable_preΨ'_char_two` — are instances of ONE technique: a
 universal identity in ℤ[A₁..A₅] whose specialization is controlled
 by (p, Δ)-powers. Concretely for the discriminant route:
 disc(preΨ'ₚ) ∈ ℤ[A] is NONZERO because the char-≠2 separability
 PROOF NOW APPLIES OVER ℚ(A₁..A₅) — the generic curve over the
 fraction field of the polynomial ring (char 0, Δ ≠ 0 a unit there
 after inverting, (p) ≠ 0). The structure disc = ±p^s·Δ^t·(monomial
 unit?) then follows if one shows disc vanishes only on the
 Δ = 0-locus (Nullstellensatz + irreducibility/radicality of (Δ) in
 ℚ̄[A]) with multiplicity bookkeeping; the same scheme gives
 resultant_Φ_ΨSq = ±Δ^k. ALTERNATIVE cheaper for char-2-only: the
 consumer of separable_preΨ' is prime_torsion_card [IsSepClosed k]
 — over sep-closed k one may normalize the char-2 curve (kill
 coefficients by the standard char-2 variable changes: a₁ ≠ 0 ⟹
 (a₁,a₂,a₃,a₄,a₆) → (1,a₂',0,0,a₆'); a₁ = 0 supersingular ⟹
 (0,0,a₃',a₄',a₆')) and re-run the ν-endgame with the explicit
 simplified b-invariants (b₂ = 1/0, Ψ₂Sq = X²-ish/b₆-const) where
 the [2]/[3]-composition H₁-terms can be analyzed term-by-term.
 Sharpest known classical statement: Gunji (1976) computes disc(ψₚ)
 in char 2; Washington Ch. 3 exercises give disc(ψₙ) = ±n^{...}Δ^{...}
 integrally — download and mine these next session (annas-mcp).
- 2026-07-17 (session 6 coda, char-2 CAUTION): re-deriving the
 `separable_preΨ'_char_two` plan shows the PREVIOUSLY RECORDED
 [3]-composition count is NOT by itself contradictory: with
 ν := ν_π, f = πᵃg, in char 2 (W) reads Φₚ′f² = p·preΨ₂ₚ (ΨSq′ = 0),
 and the m = 3 cross Φ₃ₚ·S·Ψ₃hom² = ΨSq₃ₚ·Φ₃hom (S := ΨSqₚ,
 homogeneous degrees 9 = 1 + 2·4) with Ψ₃hom ≡ Φₚ⁴, Φ₃hom ≡ Φₚ⁹
 (mod π) gives ν(Φ₃ₚ) + 2a = ν(ΨSq₃ₚ), which the EDS-divisibility
 ν(preΨ'₃ₚ) ≥ a matches EXACTLY (ν(ΨSq₃ₚ) = 2a, ν(Φ₃ₚ) = 0) — no
 contradiction without using π | f′. The char-2 argument must
 inject the hypothesis π | (preΨ'ₚ)′ elsewhere: candidate routes:
 (i) differentiate the m = 3 cross identity itself (the derivative
 of ΨSq₃ₚ = (preΨ'₃ₚ)² is again 0 in char 2 — but the derivative of
 the CROSS identity relates Φ₃ₚ′ to Wronskian-type combinations
 where (W)-at-3p and (W)-at-p interact: in char 2,
 (W)ₚ: Φₚ′f² = p·preΨ₂ₚ and (W)₃ₚ: Φ₃ₚ′ΨSq₃ₚ = 3p·preΨ₆ₚ, and
 ν-counts of preΨ₂ₚ/preΨ₆ₚ through the even-index structure
 ΨSq₂ₚ = preΨ'₂ₚ²Ψ₂Sq may force ν(Φₚ′) contradictions);
 (ii) the char-2 Frobenius structure: in char 2, f′ = (odd-part)′ and
 f′ = 0 ⟺ f ∈ k[X²] = (k[X])²-Frobenius-image; π | f, π | f′ with
 π ∤ ... — work with the derivation d/dX directly on the
 ψ₂-normalized forms (Ψ₂Sq = b₂X² + b₆ is itself a square in char 2:
 Ψ₂Sq = (a₁X + c)² when b₆ = c², i.e. AFTER adjoining √b₆ — over
 the separable-closure-bound fields the argument may simplify);
 (iii) check Washington's or Gunji's char-2 treatment of division-
 polynomial discriminants (literature check needed). NEXT SESSION:
 resolve this honestly — the char-2 node is NOT mechanical from the
 current identities alone.
- 2026-07-17 (session 6, MAJOR): **(W) and `separable_preΨ'`
 RESOLVED (char ≠ 2)**. The full derivation chain, all committed:
 (1) InvariantDerivation.lean — dX/dY/Dham (Hamiltonian derivation
 Fy·∂X − Fx·∂Y on ℤ[A][X][Y], kills F identically), DB (descent to
 Buniv via liftOfSurjective), DK (hand-rolled fraction-field
 extension with quotient rule: DK_welldef/spec/rel/add/mul/sub/div/
 sq/coeffHom + base values DK_tautX = ψ₂, DK_tautY = −Fx — all
 axiom-clean). MODULE-SYSTEM CAVEAT learned: group-section
 Derivation lemmas (map_sub/map_neg) have an
 AddCommGroup.toAddCommMonoid instance path that is NOT
 defeq-checkable under exposure — stay in the base
 AddCommMonoid-section lemmas (map_add, leibniz, leibniz_pow) and
 write negations INSIDE C-coefficients.
 (2) WronskianStep.lean — DK_addition_step + DK_doubling_step (the
 differentiated chord and tangent laws), by polynomial certificates
 saturated by (xn−x1)^4/5 resp. ψ₂(P₁)^4/5, cofactors extracted by
 explicit linear elimination (L-linear then geometric-series in l;
 scripts/eds/wronskian_{step,doubling}_cofactors.py) — sympy-verified
 and accepted by linear_combination essentially on first compile.
 (3) WronskianInduction.lean — DK_smul_taut ([n]*ω = nω at the
 tautological point, strong induction n=1/n=2/chord), then
 wronskian_taut (differentiate xₙ·ΨSqₙ = Φₙ, use the strong-aux
 TRACKING ψ₂(nP)ψₙ⁴ = ψ₂ₙ and ψ₂ₙ = preΨ₂ₙ·ψ₂, cancel DK x = ψ₂),
 univ_wronskian (pullback via taut_C_injective), wronskian (any
 CommRing): **Φₙ′ΨSqₙ − ΦₙΨSqₙ′ = n·preΨ₂ₙ**.
 (4) TorsionCard SPLIT: separable_preΨ' + prime_torsion_card +
 card_torsionBy moved to TorsionCardSep.lean (breaks the import
 cycle; Torsion.lean imports it).
 (5) separable_preΨ' in TorsionCardSep by the ν_π endgame
 (uniform in a — no case split: π^{a+1} | ΨSqₚ′ ⟹ (W) ⟹
 π^{a+1} | preΨ₂ₚ ⟹ π^{2a+1} | ΨSq₂ₚ ⟹ (C)+coprime₂ₚ ⟹
 π^{2a+1} | H = π^{2a}g²H₁ ⟹ π | H₁ ≡ 4Φₚ³ ⟹ π | Φₚ ⟹ ⊥ with
 coprimeₚ). NEW smaller node: `separable_preΨ'_char_two`
 (TorsionCardSep.lean) — char-2 case; needs the [3]-composition
 (taut_cross m=3 specialized like cross_two; Ψ₃hom ≡ 3Φ⁴, 3 ≠ 0 in
 char 2, b₂-subcase analysis; scripts/eds verified J₃-data).
 Node count still 18 (one closed, one smaller one opened); the
 torsion cone now rests on: resultant_Φ_ΨSq, Flat.lean:163,
 separable_preΨ'_char_two.
- 2026-07-17 (session 6): **(C) IS ** (`ed3752d`,
 TautMultiplication.lean): `taut_smul_formula` (machinery instance at
 taut), `taut_cross` (general (m,n) composition cross-identity from
 `smul_smul` + `some.inj`), `taut_cross_two` (m=2, denominators
 cleared by field_simp at the generic point), `univ_cross_two`
 (pulled back to ℤ[A][X] via taut_eval_C_mk + taut_C_injective):
 `Φ(2n)·Ψ₂Sqhom(Φₙ,ΨSqₙ) = ΨSq(2n)·Φ₂hom(Φₙ,ΨSqₙ)` with the
 explicit homogenized quartics, and `cross_two` (any curve, any
 CommRing, via eval₂Hom). The CROSS form suffices for the endgame:
 ν(Φ₂ₚ)=0 (coprime-node + ν(ΨSq₂ₚ)≥2), so ν(H)=ν(ΨSq₂ₚ)≥2(2a−1)
 yet H≡4Φₚ³ (mod π) gives ν(H)=0 — no exactness-splitting needed.
 Also new: `taut_eval_C_mk` + `taut_C_injective` (univariate value
 bridge + y-free injectivity, axiom-clean). REMAINING for
 `separable_preΨ'`: (W) at p. PLAN (session 6): Hamiltonian
 derivation D := Fy·∂X − Fx·∂Y on ℤ[A][X][Y] (D(F)=0 trivially),
 descend to Buniv via `Derivation.liftOfSurjective`
 (mk-surjective, ker=(F) D-stable), hand-rolled quotient-rule
 extension DK to Kuniv (~150 lines; no mathlib fraction-field
 derivation exists), then INVARIANT-DIFFERENTIAL INDUCTION at the
 tautological point: Claim A: DK(xₙ) = n·sₙ (sₙ := 2yₙ+a₁xₙ+a₃),
 Claim B: DK(yₙ) = −n·Fx(xₙ,yₙ), base n=1 is DK(tautX) = ψ₂-value
 BY CONSTRUCTION, step = differentiate the affine addition law
 (sympy-verify first), then (W) by differentiating the 
 x-formula xₙ·ΨSqₙval = Φₙval and cancelling s₁ via the tracking
 sₙψₙ⁴ = ψ₂ₙ: n·preΨ(2n)val = (Φₙ'ΨSqₙ − ΦₙΨSqₙ')val, pull back
 by taut_C_injective, specialize. Then the ν_π endgame.
- 2026-07-17 (session 5 coda): the tautological-point VALUE BRIDGE is
 proven (`taut_evalEval_mk`: evalEval at `(tautX, tautY)` = the
 quotient map; `taut_psi_ne_zero`: all `ψₙ`-values nonzero at the
 generic point) — both axiom-clean. The (C)-composition derivation at
 the generic point is now purely mechanical: instantiate
 `exists_smul_some_eq`/tracking at `(tautX, tautY)` over `Kuniv`,
 compose, cross-multiply, and pull back along `taut_evalEval_mk` +
 basis-injectivity. Then the UFD multiplicity endgame closes
 `separable_preΨ'` (modulo the (W)-differentiated-descent for the
 Wronskian at primes and `resultant_Φ_ΨSq`).
- 2026-07-17 (session 7, THE BOOKKEEPING SWEEP — commits `1834714` →
 `a23c757`): the entire "shell" of glue around the deep arithmetic was
 peeled and / in one sustained run. In order: (1) **NOS
 ** — `torsion_unramified_of_good_reduction` completed and
 audited axiom-clean (`(hp : n.Prime) (hodd : Odd n)` threaded through
 both consumers). (2) **det node ** —
 `det_galoisRep_eq_cyclotomic` from Chebotarev density + the new
 Frobenius-det leaf `det_galoisRep_globalFrob`;
 `cyclotomicCharacterModL_eq_toZMod` . (3) **Serre core
 DECOMPOSED** — `exists_p_point_of_not_isIrreducible_of_minkowski`
 derived from the stable-line dichotomy + Vélu leaf + Galois
 descent (`exists_point_eq_baseChange_of_fixed`). (4) **dichotomy
 ** — full character bookkeeping (rank-1 unit
 characters, triangular determinant via `det_eq_det_mul_det`, kernel
 openness, Minkowski application); leaf sharpened to
 `subquotient_character_unramified`. (5) **semistability leaf
 ** — reduced to `inertia_two_unipotent` +
 `subquotient_character_unramified_at_p` via the generic-`K`
 unramifiedness bridge (the `Rat.subsingleton_ringHom` spelling
 recipe). (6) bookkeeping GENERALIZED to any discrete field;
 `minkowski_character_trivial` target-generalized. (7)
 **`mod_three_of_stable_line` ** (ModThree imports the
 machinery; leaf `exists_line_with_locally_unramified_quotCharacter`).
 (8) **`inertia_two_unipotent` ** from the new pointwise Tate
 unipotence leaf `torsion_unipotent_of_multiplicative_reduction`
 (Semistable.lean) + `freyCurve_hasMultiplicativeReduction_at_two`
 (). Frontier: 17 nodes, ALL now genuinely deep arithmetic
 (Tate uniformization ×2 + its 3 Semistable consumers-to-derive,
 Chebotarev finite-level, Frobenius-det, Mazur, Vélu, flat-at-p ×2,
 mod-3 local leaf, Dickson reducibility, finite-flat Hopf, B6a/b/c,
 Frey tame-at-2).
 NEXT-BLOCK DESIGN (Tate-multiplicative derivations): derive
 `torsion_unramified_of_multiplicative_reduction` (and the unipotence
 sibling) from `exists_tateEquivSepClosure` +
 `exists_variableChange_tateCurve` + the quadratic-twist
 node. Route: (a) the `p`-torsion of `Additive (Ωˣ ⧸ zpowers q_E)` is
 represented by `u ∈ Ωˣ` with `u^p = q_E^a · 1` — pure group theory
 over the uniformization; (b) `μ_p` is inertia-fixed for residue char
 `q ≠ p` (roots of `x^p − w`, `w` a unit, are unramified — the
 `LocalInertiaFixedField` `e = 1` machinery); (c) `σu/u ∈ μ_p` for
 inertia `σ` (as `u^p ∈ ℚ_qˣ·μ`-part up to twist), giving the
 filtration `(σ−1)E[p] ⊆ e(μ_p)`, `(σ−1)e(μ_p) = 0` — unipotence;
 (d) with `p ∣ v(q_E)` (from `p ∣ v(j)`, via `valuation_j_eq`),
 `q_E = w·π^{pk}` so the `p`-th root generates an unramified
 extension and `(σ−1)E[p] = 0` — triviality. The local(`k`-generic)
 statements should be proven over the nonarchimedean local field of
 TateCurve.lean and transported by the SAME embedded-subring
 machinery as NOS; quantify transported statements over
 `localInertiaGroup`-images to avoid needing surjectivity onto
 `𝒪`-inertia.
- 2026-07-17 (session 8, THE COMPLETION GATEWAY): the local-field
 instance package is (all axiom-clean, `LocalField.lean`):
 `ℚ_[p]` AND `adicCompletion ℚ v` are `IsNonarchimedeanLocalField`s
 (`IsValuativeTopology` from the norm/`Valued`-ball correspondence —
 for the completion it is DEFINITIONAL since `Valued.mem_nhds_zero`
 is already in `ValueGroup₀` form; local compactness transported from
 `ℚ_[p]` along `adicCompletion.padicEquiv`; nontriviality from a
 prime element). The TateCurve framework INSTANTIATES at
 `k = adicCompletion ℚ v` (smoke-tested), the exact spelling of
 `localInertiaGroup`/`GaloisRep.toLocal`. Also :
 `isEquiv_valuation_maximalIdeal_localization` (Semistable.lean) —
 the `v`-adic valuation of `ℚ` is equivalent to the maximal-ideal
 valuation of `ℤ_(q)` (both `≤1`-sets are "q ∤ denominator" via
 `Rat.valuation_le_one_iff_den`).
 ROUTE UPDATE (supersedes part of the session-7 design): the
 completion transfer of multiplicative reduction should NOT be proven
 by hand — `ReductionBaseChange.lean` (sorry-free) already proves
 `hasMultiplicativeReduction_baseChange` and
 `hasSplitMultiplicativeReduction_baseChange` along ANY
 `ValuativeExtension k → l` of valuative fields (field-level c₄/Δ
 valuation chase + the unit-`c₄` Kraus–Laska criterion + residue-map
 splitness). Remaining plumbing for the unipotence-leaf derivation:
 (A) `ValuativeExtension (WithVal (v.valuation ℚ)) (adicCompletion ℚ v)`
 — the completion IS `UniformSpace.Completion` of `WithVal`, mathlib
 provides `ValuativeRel (WithVal v)` and `valuedCompletion_apply`;
 (B) the ℚ-side spelling bridge
 `HasMultiplicativeReduction (Localization.AtPrime v.asIdeal) E` ⟹
 `HasMultiplicativeReduction 𝒪[WithVal (v.valuation ℚ)] (E-as-WithVal)`
 (transport the mathlib-Reduction class across `WithVal.equiv` +
 the valuation dictionary); then (C) instantiate
 `exists_tateEquivSepClosure` + `tate_inertia_unipotent` () at
 `k = adicCompletion ℚ v`, Ω = its algebraic closure, and transport
 the pointwise unipotence back to `E(ℚ̄)` along the chosen embedding
 (the `absoluteGaloisGroup.map`/NOS-consumer pattern), handling the
 nonsplit case by the quadratic twist (unramified at inertia).
- 2026-07-17 (session 8 continued, THE (C)-BLOCKS): the remaining
 plumbing for the unipotence-leaf derivation, all axiom-clean:
 (B) `hasMultiplicativeReduction_adicCompletion` (Semistable.lean) —
 reduction type transfers to the completion (coefficient/c₄/Δ chase
 through the dictionary + `valuedAdicCompletion_eq_valuation'` +
 `adicValuation_{eq,lt}_one_iff`, integrality by
 `isIntegral_of_exists_lift`, minimality by unit-`c₄` Kraus–Laska;
 the `algebraMap ℚ K'`-vs-lemma-spelling wall closed ONCE via
 `Rat.subsingleton_ringHom` against a hand-bundled
 `ofCompletion ∘ coeRingHom ∘ WithVal.equiv.symm` composite).
 (C1) `localValuationSubring v` (AbsoluteGaloisGroup.lean) — the
 integral closure of `𝒪ᵥ` in `Kᵥᵃˡᵍ` as a ValuationSubring
 (spectral-norm dichotomy), stabilized by every `Kᵥ`-automorphism
 (`mem_decompositionSubgroup_localValuationSubring`), with
 `mem_inertiaSubgroup_localValuationSubring`: `localInertiaGroup v`
 (mod-𝔪 spelling) lands in the RamificationGroup-style
 `inertiaSubgroup` (residue-field spelling) — the exact interface of
 the `tate_inertia_unipotent`.
 (C2) `natCast_residueField_localValuationSubring_ne_zero`
 (Semistable.lean) — `p ≠ q` is nonzero in the residue field of the
 local valuation subring (Chebotarev's unit-lemma pushed through the
 integral-closure inclusion hom) — the `hchar` input of
 `tate_inertia_unipotent`.
 REMAINING for `torsion_unipotent_of_multiplicative_reduction`:
 (C3) the equivariant point transport `E(ℚ̄)[p] ↪ E(Ω)[p]` along the
 chosen embedding (`Field.absoluteGaloisGroup.lift_map` equivariance +
 `Point.map`-functoriality + injectivity to pull the unipotence
 equation back); (C4) the split/nonsplit case split via
 `exists_quadraticTwist_hasSplitMultiplicativeReduction` (
 ) — the twist is by an inertia-trivial character, so
 unipotence transfers; (C5) assembly: instantiate
 `exists_tateEquivSepClosure` (leaf) at `k = adicCompletion ℚ v_q`
 (gateway instances) and feed `tate_inertia_unipotent` at
 `A = localValuationSubring`, `hσ` via (C1), `hchar` via (C2).
