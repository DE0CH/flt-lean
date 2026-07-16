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

## Tree (✓ = proven here or in mathlib, ✗ = sorry, ○ = in progress, □ = not yet started)

- `fermat_last_theorem : FermatLastTheorem`
  - ✓ `FermatLastTheorem.of_odd_primes` (mathlib, NumberTheory/FLT/Four.lean)
  - ✓ `fermatLastTheoremFour` (mathlib)
  - ✓ `fermatLastTheoremThree` (mathlib)
  - ✓ `fermatLastTheoremFor_of_five_le : ∀ p, p.Prime → 5 ≤ p → FermatLastTheoremFor p`
    (`Fermat/PrimeFive.lean`) — proven from:
    - ✓ `FreyPackage` + `FreyPackage.of_not_FermatLastTheoremFor_p_ge_5` +
      `FreyPackage.fermatLastTheoremFor_p_ge_5` (`Fermat/FreyPackage.lean`,
      adapted from the FLT project, Apache 2.0) — a counterexample for prime
      `p ≥ 5` normalizes to a Frey package (coprime, `a ≡ 3 mod 4`, `b` even).
      Fully proven, no sorry.
    - ✓ `FreyPackage.freyCurve : WeierstrassCurve ℚ` with `IsElliptic`
      instance, `Δ`, `b₂`, `b₄`, `c₄`, `j`, and
      `FreyCurve.j_valuation_of_bad_prime` (`Fermat/FreyCurve.lean`, adapted
      from the FLT project). Fully proven, no sorry.
    - ✓ `FreyPackage.false : FreyPackage → False` — now PROVEN from Mazur +
      B4 (mirroring the FLT project's `Proof.lean` boss-theorem spine):
      - ✓ `FreyPackage.mazur` (`Fermat/FLT/FreyCurve/Mazur.lean`) — the mod-p
        rep of the Frey curve is irreducible — now DERIVED (2026-07-16) from
        two explicit nodes in `Fermat/FLT/FreyCurve/MazurTorsion.lean` (own
        work), following Serre (Duke 1987, §4.1):
        - ✓ `FreyPackage.exists_torsion_embedding_of_not_isIrreducible` —
          DERIVED (2026-07-16) from the two nodes below: Serre's
          analysis produces full 2-torsion plus a rational point of
          order p on some curve; the PROVEN `embedding_assembly`
          combines them into an injective ℤ/2 × ℤ/2p via CRT.
          - ✓ `FreyPackage.exists_two_torsion_and_p_point_of_not_isIrreducible`
            — DERIVED (2026-07-16) from the disjunction node below plus
            the PROVEN Frey 2-torsion.
            - ✓ `FreyPackage.exists_p_point_of_not_isIrreducible` —
              DERIVED (2026-07-16): the Minkowski input is discharged
              by the node below.
              - ✓ `minkowski_character_trivial` — DERIVED (2026-07-16)
                from the subgroup form below: the kernel is an open
                normal subgroup containing every inertia image
                (`Subgroup.map_le_iff_le_comap` + `ker (χ∘res) =
                comap res (ker χ)`), hence everything, so χ = 1.
                - ✓ `open_normal_subgroup_eq_top_of_inertia_le` —
                  **Minkowski, subgroup form**: DERIVED (2026-07-16)
                  from the inertia dictionary below plus mathlib's
                  discriminant theory (fixed field of the open normal
                  kernel via the infinite Galois correspondence;
                  finite Galois number field by
                  `isOpen_iff_finite`/`normal_iff_isGalois`;
                  `1 < finrank` from `H ≠ ⊤`;
                  `exists_not_isUnramifiedAt_int_of_isGalois` gives an
                  everywhere-ramified prime `p`; going-up lifts it;
                  the dictionary contradicts).
                  - ✗ `isUnramifiedAt_of_inertia_le_fixingSubgroup` —
                    **THE inertia dictionary** (the shared bridge; also
                    what the five glue nodes need): if the image of
                    `localInertiaGroup q` in G_ℚ fixes the finite
                    extension `L` pointwise, every prime of `𝒪 ⊇ ℤ`
                    (integral closure in `L`) above `q` is
                    `Algebra.IsUnramifiedAt ℤ`.
              - ✗ `FreyPackage.exists_p_point_of_not_isIrreducible_of_minkowski`
                — Serre's analysis with the Minkowski input as a
                hypothesis: stable line ⟹ characters χ₁χ₂ = ω̄;
                semistability ⟹ one character everywhere unramified ⟹
                trivial by hypothesis; χ₁ = 1: p-point on the Frey
                curve; χ₂ = 1: package on the Vélu quotient.
                Remaining deep content:
                - □ quotients of elliptic curves by finite rational
                  subgroups (Vélu) — needed for the χ₂ = 1 case.
                - ✓ `exists_stable_line_of_not_isIrreducible`
                  (`Chebotarev.lean`, PROVEN sorry-free 2026-07-16) —
                  the first step: a non-irreducible 2-dim mod-ℓ rep
                  has a Galois-stable line.
            - ✓ `FreyPackage.freyCurve_two_torsion_embedding` — PROVEN
              (2026-07-16): the Frey model has rational 2-torsion
              points (0, 0) and (aᵖ/4, −aᵖ/8) (the quadratic factors
              as (x − aᵖ/4)(x + bᵖ/4)); they are distinct, of order 2
              (fixed by negation `negY`), and generate an injective
              (ℤ/2)² →+ E(ℚ) via two `ZMod.lift`s and a coprod, with
              injectivity by the four-element case analysis.
          - ✓ `embedding_assembly` (PROVEN 2026-07-16): in an abelian
            group, an injective (ℤ/2)² and an element of order exactly
            p (odd prime) assemble into an injective ℤ/2 × ℤ/2p
            (`ZMod.chineseRemainder`; the parts are separated by the
            coprime annihilators 2 and p).
        - ✓ `WeierstrassCurve.mazur_torsion_bound` — Mazur's torsion
          theorem, weak form: no elliptic curve over ℚ has a subgroup of
          rational points ≅ ℤ/2 × ℤ/2p for p ≥ 5 (primality dropped as
          unneeded) — now PROVEN (2026-07-16) from the faithful
          classification below: images of an injective hom from the finite
          group ℤ/2 × ℤ/2p are torsion (finite additive order), the hom
          corestricts into the torsion submodule, and 4p ≥ 20 > 16 ≥ the
          order of every group in Mazur's list (`Nat.card` comparison).
          - ✗ `WeierstrassCurve.mazur_classification` — **Mazur's torsion
            theorem**, stated faithfully: the torsion submodule
            (`Submodule.torsion ℤ E(ℚ)`) is ≃+ to one of the fifteen
            groups ℤ/n (n ∈ {1,…,10,12}) or ℤ/2 × ℤ/2m (m ∈ {1,…,4}).
            Mazur, Publ. Math. IHÉS 47 (1977); Invent. Math. 44 (1978).
      - ✓ `FreyPackage.galoisRep_not_irreducible` (B4, `Fermat/PrimeFive.lean`)
        — now DERIVED (2026-07-16) from two explicit nodes, mirroring the
        FLT project's hardly-ramified plan (their B5/B6, stated in Lean here
        before upstream):
        - ✓ `FreyCurve.torsion_isHardlyRamified`
          (`GaloisRepresentation/HardlyRamified/Frey.lean`) — now DERIVED
          (2026-07-16) as the structure constructor applied to the four
          defining conditions, each an explicit node in
          `HardlyRamified/FreyConditions.lean` (own work):
          - ✓ `FreyCurve.torsion_det` — det ρ̄ = mod-p cyclotomic
            character — now DERIVED (2026-07-16) via the Weil pairing
            route (`EllipticCurve/WeilPairing.lean`, own work):
            - ✗ `WeilPairing.exists_weilPairing` — **the Weil pairing**:
              an alternating, nondegenerate, `ZMod p`-bilinear pairing on
              `E[p]` scaled by the Galois action through the cyclotomic
              character (`E[p] ∧ E[p] ≅ μ_p`).
            - ✓ `WeilPairing.pairing_map_eq_det_smul` +
              `WeilPairing.det_eq_of_conj` — PROVEN (sorry-free): on a
              2-dimensional space an alternating form transforms under
              any endomorphism by the determinant (basis + 2×2
              computation), so scaling by `c` forces `det = c`.
          - ✓ `FreyCurve.torsion_isUnramified` — unramified outside
            {2, p}: DERIVED (2026-07-16) by the case split `q ∣ abc` or
            not, from the two nodes below.
            - ✓ `FreyCurve.torsion_isUnramified_of_good` — DERIVED
              (2026-07-16) from the two `FreyCurve/Semistable.lean`
              nodes below.
              - ✓ `FreyPackage.freyCurve_hasGoodReduction_of_not_dvd`
                (`FreyCurve/Semistable.lean`, own work): PROVEN
                (2026-07-16) — at odd `q ∤ abc` the Frey equation is
                `q`-integral (integrality via `freyCurveInt` +
                `FreyCurve.map`) with unit discriminant
                `(abc)^{2p}/2⁸` (numerator and denominator prime to
                `q`, hence a unit of `ℤ_(q)`; adic valuation `1` via
                `mker_valuation_eq_isUnitSubmonoid`), hence minimal
                (valuation `1` is maximal among integral models) with
                good reduction over `ℤ_(q) = Localization.AtPrime`.
              - ✗ `WeierstrassCurve.isUnramifiedAt_of_hasGoodReduction`
                (`FreyCurve/Semistable.lean`, own work): the NOS
                local-global glue — good reduction at `q ≠ p` gives
                `IsUnramifiedAt q` for the mod-`p` torsion rep; to be
                closed against the vendored NOS node below (inertia
                dictionary between `localInertiaGroup` and valuation
                subrings of `ℚ̄`).
                - ✗ `torsion_unramified_of_good_reduction`
                  (`KnownIn1980s/EllipticCurves/GoodReduction.lean`,
                  vendored 2026-07-16): the NOS easy direction — good
                  reduction over a DVR makes the inertia action on
                  `n`-torsion trivial.
            - ✓ `FreyCurve.torsion_isUnramified_of_multiplicative` —
              DERIVED (2026-07-16) from the PROVEN arithmetic
              (`freyCurve_hasMultiplicativeReduction_of_dvd` +
              `j_valuation_of_bad_prime`) and the Tate glue node below.
              - ✓ `FreyPackage.freyCurve_hasMultiplicativeReduction_of_dvd`
                (`FreyCurve/Semistable.lean`, own work): PROVEN
                (2026-07-16) — at odd `q ∣ abc` the equation is
                `q`-integral, `c₄ = c^{2p} - (ab)^p` is prime to `q`
                (pairwise coprimality forces exactly one of `ab`, `c`
                divisible by `q`), so `v(c₄) = 1` (minimality by the
                vendored unit-`c₄` Kraus–Laska criterion) while
                `Δ = (abc)^{2p}/2⁸` lies in the maximal ideal.
              - ✗ `WeierstrassCurve.isUnramifiedAt_of_hasMultiplicativeReduction`
                (`FreyCurve/Semistable.lean`, own work): the Tate glue
                — multiplicative reduction at odd `q ≠ p` with
                `p ∣ v_q(j)` ⟹ `IsUnramifiedAt q`; to be closed
                against the quadratic-twist (vendored PROVEN) and
                Tate-uniformization (`exists_tateEquivSepClosure`)
                nodes.
          - ✓ `FreyCurve.torsion_isFlat` — flat at p: DERIVED
            (2026-07-16) by the case split `p ∣ abc` or not, from the
            two nodes below.
            - ✓ `FreyCurve.torsion_isFlat_of_good` — DERIVED
              (2026-07-16) from the PROVEN arithmetic node
              `freyCurve_hasGoodReduction_of_not_dvd` (applied at
              `q := p`) and the flat glue node below.
              - ✗ `WeierstrassCurve.isFlatAt_of_hasGoodReduction`
                (`FreyCurve/Semistable.lean`, own work): good reduction
                at `p` ⟹ `IsFlatAt p` for the mod-`p` torsion rep; to
                be closed against the vendored
                `torsion_flat_of_good_reduction` (transport of the
                Hopf-algebra prolongation package along
                `ℤ_(p) → ℤ_p`).
              - ✗ `torsion_flat_of_good_reduction`
                (`KnownIn1980s/EllipticCurves/Flat.lean`, vendored
                2026-07-16): good reduction over a DVR makes the
                `n`-torsion a finite flat group scheme (Hopf algebra,
                finite flat, étale generic fibre, equivariant points
                isomorphism). Plus two division-polynomial nodes:
                ✗ `resultant_Φ_ΨSq` and ✓ `isCoprime_Φ_ΨSq` (DERIVED
                2026-07-16 from the resultant node via mathlib's
                `exists_mul_add_mul_eq_C_resultant` Bézout identity).
            - ✓ `FreyCurve.torsion_isFlat_of_multiplicative` — DERIVED
              (2026-07-16) from the PROVEN arithmetic
              (`freyCurve_hasMultiplicativeReduction_of_dvd` at
              `q := p` + `j_valuation_of_bad_prime`) and the glue node
              below.
              - ✗ `WeierstrassCurve.isFlatAt_of_hasMultiplicativeReduction`
                (`FreyCurve/Semistable.lean`, own work): the
                peu-ramifiée glue — multiplicative reduction at `p`
                with `p ∣ v_p(j)` makes the Tate-curve extension
                `0 → μ_p → E[p] → ℤ/p → 0` peu ramifiée, which
                prolongs to a finite flat group scheme over `ℤ_p`.
          - ✓ `FreyCurve.torsion_isTameAtTwo` — DERIVED (2026-07-16)
            from the PROVEN arithmetic and the tame glue node below.
            - ✓ `FreyPackage.freyCurve_hasMultiplicativeReduction_at_two`
              (`FreyCurve/Semistable.lean`, own work): PROVEN
              (2026-07-16) — the Frey model is semistable at 2 by
              design: `c₄ = c^{2p} - (ab)^p` is odd (`a ≡ 3 mod 4`,
              `b` even force `c` odd), giving `v(c₄) = 1` and
              Kraus–Laska minimality; `Δ = 2^{2p-8}(ab'c)^{2p}` (with
              `b = 2b'`) is in the maximal ideal since `2p > 8`.
            - ✗ `WeierstrassCurve.isTameAtTwo_of_hasMultiplicativeReduction`
              (stated in `FreyConditions.lean` for a general elliptic
              curve over ℚ): the Tate glue at 2 — multiplicative
              reduction at 2 and `p` odd give the rank-1 unramified
              quotient with character squaring to 1; to be closed
              against the quadratic-twist (vendored PROVEN) and
              Tate-uniformization (`exists_tateEquivSepClosure`)
              nodes.
            - ✓ `TateParameter.lean` vendored (2026-07-16, ZERO
              sorries — fully proven): the formal q-expansion machinery
              (formal `c₄`, `Δ`, `j⁻¹` power series and the Tate
              parameter as evaluation), plus the two ValuativeRel
              `FLT.Mathlib` prerequisites (also sorry-free). Feeds the
              Tate-curve chain (`TateCurve.lean` etc.) next.
            - ✓ Tate-curve/reduction batch vendored (2026-07-16, ZERO
              sorries — all fully proven): `TateCurveConstruction.lean`
              (1551 lines: the Tate curve `E_q` over a nonarchimedean
              local field, its q-expansions via
              `Slop/NumberTheory/TsumDivisorsAntidiagonal.lean`),
              `TateCurveBaseChange.lean` (E_q commutes with base
              change), `ReductionBaseChange.lean` (multiplicative
              reduction transfers along finite extensions; Kraus–Laska
              minimality criterion), the mathlib overlay
              `Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean`,
              and four `FLT.Mathlib` prerequisites
              (QuadraticDiscriminant, Splits, Weierstrass DVR overlay,
              IsDiscreteValuationRing). Remaining for this branch:
              `TateCurve.lean` (upstream `tateCurveEquiv` is sorry-d
              DATA — must be reformulated existentially before
              vendoring, as done for the Weil pairing).
        - ✓ **B5** `GaloisRepresentation.not_isIrreducible_of_isHardlyRamified`
          (`GaloisRepresentation/HardlyRamified/Reducible.lean`, own work) —
          now DERIVED (2026-07-16) from three explicit nodes in
          `HardlyRamified/Lift.lean` (own work), following Buzzard's 2026
          EPSRC Lecture 4 (his B5a/B5b/B5c):
          - ✗ **B6a** `exists_hardlyRamifiedLift` — an irreducible hardly
            ramified mod-ℓ rep (ℓ ≥ 5) lifts to a hardly ramified ℓ-adic
            rep over the integers `O` of a finite extension of `ℚ_ℓ`
            (bundled in `structure HardlyRamifiedLift`: `O` + framed rep +
            reduction map + Frobenius-charpoly compatibility). Deformation
            theory / modularity lifting without residual modularity.
          - ✓ **B6bc** `residual_charFrob_eq` — the residual Frobenius
            charpolys of a liftable rep are those of `1 ⊕ χ̄`
            (`X² − (q+1)X + q`) — now DERIVED (2026-07-16) from the
            faithful split (vendored from the FLT project's newer layer):
            - ✗ **B6b** `IsHardlyRamified.mem_isCompatible`
              (`HardlyRamified/Family.lean`, vendored; conclusion named
              `IsInHardlyRamifiedFamily` as a marked VENDORING CHANGE) — a
              hardly ramified ℓ-adic rep lives in a compatible family
              (`GaloisRepFamily.lean`, vendored defs, sorry-free) all of
              whose odd members are hardly ramified. STRENGTHENED
              (2026-07-16): the package now records injectivity of the
              coefficient-ring embeddings into `ℚ̄_p` — an audit of the
              glue's proof skeleton showed the upstream statement is too
              weak for the charpoly descent (algebraMap from a domain to
              a field need not be injective); true for the intended
              subrings of `ℚ̄_p`.
            - ✓ `residual_charFrob_eq_of_family` (own work, `Lift.lean`)
              — compatibility BOOKKEEPING — now PROVEN (2026-07-16):
              extract the 3-adic member via the number-field embedding;
              its charpoly at Frob_q is `X² − (1+q)X + q` by B6c's trace
              + the cyclotomic determinant at Frobenius + the 2-dim
              reconstruction (generalized to comm rings); transport
              through baseChange-conj to the family, descend to the
              coefficient field by injectivity of the embedding, ride
              compatibility to the ℓ-adic member, descend to `O` by the
              strengthened-B6b injectivity, and reduce through
              `charFrob_compat`. Exceptional set: `S₀ ∪ {2-place,
              3-place}`. Consumes B6c and the ℓ-adic Frobenius-value
              node. AUDIT RESTATEMENT (2026-07-16): the conclusion (and
              B6bc's, and the Chebotarev–Brauer–Nesbitt hypothesis) now
              carries a finite exceptional set `S` of places — the
              family's `isCompatible` only pins charpolys outside an
              unspecified finite set, so the `∀ q ∉ {2,3,ℓ}` form was
              unprovable; the density argument absorbs any finite `S`
              (new sorry-free bridge:
              `toHeightOneSpectrumRingOfIntegersRat_injective`, distinct
              primes give distinct places, so a finite set of places
              excludes only finitely many primes in the auxiliary-prime
              selection). Proof ingredients consumed:
              - ✗ **B6c** `IsHardlyRamified.three_adic`
                (`HardlyRamified/Threeadic.lean`, vendored) — a 3-adic
                hardly ramified rep has trace(Frob_q) = 1 + q for q ≥ 5.
                - ✗ `IsHardlyRamified.mod_three` (`ModThree.lean`,
                  vendored 2026-07-16) — a mod-3 hardly ramified rep has
                  a Γℚ-equivariant surjection onto the trivial character
                  (extension of trivial by cyclotomic); B6c's eventual
                  proof lifts this 3-adically.
            - NB the lift structure gained an `IsModuleTopology ℤ_[ℓ] O`
              field (statement strengthening of B6a's conclusion, true for
              integers of finite extensions of ℚ_ℓ; required by B6b).
          - ✓ `not_isIrreducible_of_charFrob_eq` — Chebotarev + Brauer–
            Nesbitt — now DERIVED (2026-07-16, `Chebotarev.lean` + proof
            in `Lift.lean`): the agreement set with `1 ⊕ χ̄`'s charpolys
            is closed (module topology on `End` over `ZMod ℓ` is discrete
            — PROVEN; coefficient maps continuous) and contains the dense
            Frobenius conjugates, so Brauer–Nesbitt applies. Children:
            - ✓ `dense_conjClasses_globalFrob` — **Chebotarev density**,
              topological form — now DERIVED (2026-07-16) by the
              profinite limit argument (PROVEN: cosets of fixing
              subgroups of finite subextensions are a neighborhood basis,
              `krullTopology_mem_nhds_one_iff`; the finite-level
              statement puts a Frobenius conjugate in every coset):
              - ✗ `exists_frobenius_conj_mem_coset` — **Chebotarev,
                finite level**: for every finite subextension `E` of
                `K̄/K` and every `σ`, the coset `σ·Gal(K̄/E)` contains a
                conjugate of a `globalFrob v` with `v ∉ S` (existence
                form of Chebotarev for the Galois closure of `E/K`).
            - ✓ `not_isIrreducible_of_charpoly_eq` — **Brauer–Nesbitt**,
              2-dim mod-ℓ instance — PROVEN SORRY-FREE (2026-07-16):
              Cayley–Hamilton turns the charpoly hypothesis into
              `(ρg − 1)(ρg − χ̄g) = 0`; on `H := ker χ̄` every element is
              unipotent, Kolchin gives a nonzero `H`-fixed space, stable
              under Γ (H normal); if proper it refutes irreducibility
              (`not_isIrreducible_of_invariant_submodule`, via
              `Subrepresentation`); if everything, the image commutes
              (commutators die in H) and the common-eigenvector lemma
              yields an invariant line. Children (both proven):
              - ✓ `BrauerNesbitt.exists_fixed_of_unipotent` — Kolchin,
                2-dim: a group of unipotent endomorphisms has a common
                nonzero fixed vector — PROVEN (2026-07-16, sorry-free).
                Route: matrix helpers
                `trace_eq_zero_and_det_eq_zero_of_sq_eq_zero` (square-zero
                2×2 has zero trace/det, entry computation) and
                `sandwich_of_det_eq_zero` (rank-one identity
                `N₀NN₀ = tr(NN₀)•N₀`); unipotency of `ρ g`, `ρ g₀`,
                `ρ (g g₀)` forces `tr(NN₀) = 0`, so
                `n₀ (ρ g − 1) n₀ = 0`; the line `range n₀ = ker n₀` is
                preserved with square-zero scalar action, hence fixed
                pointwise.
              - ✓ `BrauerNesbitt.exists_common_eigenvector_of_commuting`
                — a commuting family annihilated by split quadratics on
                a 2-dim space has a common eigenvector — PROVEN
                (2026-07-16, sorry-free): all-scalar case is trivial;
                otherwise a non-scalar member's eigenspace
                `ker (f₀ − a)` is nonzero (else `f₀ − b = 0` by
                injectivity), proper, hence 1-dimensional, preserved by
                commutativity, and its generator is the common
                eigenvector.
            - ✓ `cyclotomicCharacterModL_globalFrob` — χ̄(Frob_q) = q
              for q ≠ ℓ — now DERIVED (2026-07-16) by mod-ℓ reduction
              (`cyclotomicCharacter.spec` at n = 1 +
              `modularCyclotomicCharacter.unique`) from:
              - ✓ `cyclotomicCharacter_globalFrob` — the **ℓ-adic**
                cyclotomic character evaluates to q at `globalFrob q`
                (q ≠ ℓ) — now DERIVED (2026-07-16, the hardest assembly
                of the session): `lift_map` transports the action to
                `ℚ_qᵃˡᵍ`; `ℓ^k`-th roots of unity are integral
                (`IsIntegral.of_pow`); `apply_of_pow_eq_one` at the
                maximal ideal of the integral closure gives the q-power
                action (exponent = q by the residue node, side condition
                by the unit node); descend by injectivity of the chosen
                embedding (forcing the adic-completion algebra instance
                against the `ratAlgebra` diamond); conclude by
                `modularCyclotomicCharacter.unique` at every level and
                `PadicInt.ext_of_toZModPow`. Serves the glue at ℓ = 3
                and ChebBN at ℓ. Children:
                DERIVATION MAPPED (2026-07-16), all ingredients in-tree:
                (i) equivariance of `absoluteGaloisGroup.map` along the
                chosen embedding — ALREADY PROVEN in the vendored tree
                as `Field.absoluteGaloisGroup.lift_map`
                (`AbsoluteGaloisGroup.lean`), and `AlgebraicClosure.map`
                is definitionally `IsAlgClosed.lift`
                (`Deformations/Lemmas.lean`);
                (ii) ✓ `natCard_residue_quotient_toHeightOneSpectrum`
                — PROVEN sorry-free (2026-07-16): the contraction of the
                maximal ideal is the maximal ideal
                (`Ideal.IsMaximal.under` on the integral closure + local
                uniqueness); transport to `ℤ_[q]` by
                `adicCompletionIntegers.padicIntEquiv` (maximal ideals
                correspond via `Ideal.comap_symm`), the `ℤ_[p]` residue
                count is `p` (`toZMod` surjective with kernel `𝔪`), and
                `natGenerator (q-place) = q` via `span_natGenerator` and
                the `ringOfIntegersEquiv` bridge. WITH THIS,
                `cyclotomicCharacter_globalFrob` and its mod-ℓ corollary
                are UNCONDITIONALLY PROVEN ([propext, Classical.choice,
                Quot.sound]); the Chebotarev–Brauer–Nesbitt chain now
                rests on the single leaf `exists_frobenius_conj_mem_coset`; (ii′) ✗
                `isUnit_natCast_adicCompletionIntegers` — PROVEN
                sorry-free (2026-07-16): a valuation-subring unit is an
                element of valuation one; the completion's valuation
                restricts to the global one, which on integers is the
                `intValuation`, equal to one iff `p ∉ v` — i.e. `p ≠ q`
                by `natCast_mem_toHeightOneSpectrum_iff`;
                (iii) `AlgHom.IsArithFrobAt.apply_of_pow_eq_one`
                (vendored `Frobenius.lean`): a Frobenius sends m-th
                roots of unity to their q-th powers when q ∤ m — apply
                at m = ℓ^k via `isArithFrobAt_adicArithFrob`;
                (iv) transport through the embedding and conclude by
                `cyclotomicCharacter.unique`-mod-ℓ^k plus
                `PadicInt.ext_of_toZModPow`.
              - ✓ `toZMod_eq_ringEquivCongr_comp_toZModPow` — PROVEN
                (kernel rigidity of ring homs into `ZMod p`).
            - ✓ sorry-free bridges (own work, `Chebotarev.lean`):
              `cyclotomicCharacterModL` (the mod-ℓ cyclotomic character,
              constructed + continuity PROVEN), `globalFrob` (+ `charFrob`
              = charpoly at `globalFrob`, rfl),
              `discreteTopology_moduleTopology` (finite module over a
              discrete ring), `exists_prime_toHeightOneSpectrum` (every
              finite place of ℚ is a prime's place),
              `monic_quadratic_ext` + comparison-quadratic coefficient
              lemmas.
      - Supporting sorries in vendored infrastructure
        (`Fermat/FLT/EllipticCurve/Torsion.lean`):
        - ✓ `n_torsion_finite` — DERIVED (re-derived 2026-07-16, second
          route): the torsion count `card_torsionBy` is `n² > 0`, and
          positive `Nat.card` forces finiteness. Statement specialized
          (VENDORING CHANGE) to separably closed characteristic-zero
          fields — the only fields at which the tree uses it (`galoisRep`
          gained `[CharZero K]`). The former division-polynomial route
          (`TorsionFinite.lean` with nodes
          `eval_ΨSq_eq_zero_of_smul_eq_zero`, `ΨSq_ne_zero_of_charDvd`,
          covering arbitrary characteristic) is SUPERSEDED and removed —
          the frontier shrinks by two nodes.
        - ✓ `n_torsion_card` (= n² over sep. closed fields, `(n : k) ≠ 0`)
          — now DERIVED (2026-07-16, `TorsionCard.lean`, own work):
          `card_torsionBy` PROVEN by strong induction peeling off the
          minimal prime factor — multiplication by `p := n.minFac`
          restricts to a surjection `E[n] → E[n/p]` with kernel `E[p]`,
          so Lagrange + the first isomorphism theorem give
          `#E[n] = p²·(n/p)²`; no CRT needed. Faithful leaves:
          - ✗ `TorsionCard.smul_surjective` — divisibility of the points
            group: `[n]` is surjective on points over a separably closed
            field for `(n : k) ≠ 0` (separable isogeny).
          - ✗ `TorsionCard.prime_torsion_card` — `#E[p] = p²` for prime
            `p` with `(p : k) ≠ 0` (kernel of the separable degree-`p²`
            isogeny).
        - ✓ `WeierstrassCurve.galoisRep` — CONSTRUCTED (2026-07-16). The
          formerly sorry-d DATA is now the genuine representation: the
          Galois action on points (`Point.map`, via the `DistribMulAction`
          instance) restricted to the `n`-torsion and made `ZMod n`-linear
          (`AddMonoidHom.toZModLinearMap`). Continuity: the coordinates of
          the (finitely many, via `n_torsion_finite`) torsion points
          generate a finite extension `F/K`; the rep kills the open
          subgroup `Gal(Kᵃˡᵍ/F)` (`fixingSubgroup_isOpen`), so every fiber
          is a union of open cosets — continuous into any topology on the
          target. `#print axioms`: sorryAx enters only through
          `n_torsion_finite`. Mazur/B4 are now statements about the REAL
          representation.
        - ✓ `group_theory_lemma` — PROVEN (2026-07-16) in
          `Fermat/FLT/EllipticCurve/TorsionCounting.lean` (own work, not
          vendored): structure theorem for finite abelian groups + torsion
          counting in `ZMod m` (`#torsionBy d (ZMod m) = gcd d m`, via the
          first isomorphism theorem) + multiset determination (each prime
          `q ∣ n` occurs exactly `r` times, each exponent forced to
          `v_q(n)`) + CRT reassembly (`ZMod.equivPi`). Axioms:
          `[propext, Classical.choice, Quot.sound]` — sorry-free.
        - ✓ `Module.Finite (ZMod n) (nTorsion n)` instance — statement was
          FALSE for `n = 0`; now requires `[NeZero n]` (marked VENDORING
          CHANGE) and is derived from `n_torsion_finite`, consolidating the
          sorry into that single node.
        - ✓ `galoisRepresentation` DistribMulAction fields (earlier layer).
      - `Fermat/FLT/GaloisRepresentation/HardlyRamified/Frey.lean`: 1 sorry
        (`torsion_isHardlyRamified` — the Frey curve's rep is hardly
        ramified, Serre §4.1 + Tate curve theory; the former second sorry,
        the rank hypothesis, was discharged by `p_torsion_rank`).

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
  **Step (1) is now PROVEN in-tree**: `finite_quotient_of_isOpen`
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
  now DERIVED; the open sorry is
  `isUnramifiedAt_of_inertia_le_fixingSubgroup` — the pure inertia
  dictionary, shared with the five glue nodes. The dictionary's core
  mechanism is already vendored PROVEN:
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
  residue field of `q.under ℤ` is `𝔽_p` (perfect ✓), so the dictionary
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
  needed.** The vendoring closure (verified): the KnownIn1980s
  EllipticCurves files plus the FLT-repo Mathlib-additions
  `FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Reduction`,
  `FLT.Mathlib.RingTheory.Valuation.ValuativeRel.Basic`,
  `FLT.Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology`,
  `FLT.Slop.NumberTheory.TsumDivisorsAntidiagonal`, and their recursive
  imports — a multi-file vendoring workstream, now fully unblocked at
  the current pin. NB `tateEquiv` (Tate's uniformization)
  is **sorry-d DATA** (a `def`), so vendoring must track it as
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
vendored as a sorry-backed theorem, then removed altogether. No node of the
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
- 2026-07-16: layer 3 — vendored the FLT project's 32-module closure under
  `Fermat/FLT/` (import-rewritten; `knownin1980s` axiom → sorry-backed
  theorem; one auto-generated instance name fixed). mathlib re-pinned to the
  FLT project's exact rev a3364faec429. `FreyPackage.false` proven from
  `mazur` + B4; sorry frontier now: B4, knownin1980s (Mazur), Torsion
  infrastructure (6), HardlyRamified/Frey (2). FLT repo cloned to
  ~/Documents/cs/FLT for reference (never build there).
  NB: the main checkout at ~/Documents/cs/dissertation was hit by an iCloud
  eviction incident (see chat log); pushes go through the rescue clone in the
  session scratchpad until the main .git re-materializes.
- 2026-07-16 (session 2): `group_theory_lemma` PROVEN sorry-free in new file
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
- 2026-07-16 (session 3, cont.): **`mazur_torsion_bound` PROVEN** from the
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
- 2026-07-16 (session 3, cont.): **B6bc split and derived** — vendored the
  FLT project's newer compatible-family layer
  (`Deformations/RepresentationTheory/GaloisRepFamily.lean`, defs,
  sorry-free; `HardlyRamified/Family.lean` = B6b `mem_isCompatible`, with
  the conclusion extracted into the named predicate
  `IsInHardlyRamifiedFamily` as a marked VENDORING CHANGE;
  `HardlyRamified/Threeadic.lean` = B6c `three_adic`). New own-work glue
  node `residual_charFrob_eq_of_family` in `Lift.lean` (compatibility
  bookkeeping; consumes B6c in its eventual proof); `residual_charFrob_eq`
  (B6bc) now PROVEN from B6b + glue. `HardlyRamifiedLift` gained an
  `IsModuleTopology ℤ_[ℓ] O` field (B6a statement strengthening, needed by
  B6b's instance context). Axiom audit clean. Sorry frontier (14, all
  Props): `exists_torsion_embedding_of_not_isIrreducible`,
  `mazur_classification`, `torsion_det`, `torsion_isUnramified`,
  `torsion_isFlat`, `torsion_isTameAtTwo`, B6a, B6b,
  `residual_charFrob_eq_of_family`, B6c, Chebotarev–Brauer–Nesbitt,
  `n_torsion_card`, `eval_ΨSq_eq_zero_of_smul_eq_zero`,
  `ΨSq_ne_zero_of_charDvd`.
- 2026-07-16 (session 3, cont.): **Chebotarev–Brauer–Nesbitt decomposition
  STARTED** (○ in progress) — new own-work file
  `GaloisRepresentation/Chebotarev.lean`: `globalFrob v : Γ K` defined
  (image of the local arithmetic Frobenius under `Γ Kᵥ → Γ K`; proven
  `charFrob v = charpoly at globalFrob v` by `rfl`), and the topological
  Chebotarev density node stated (✗ `dense_conjClasses_globalFrob`: the
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
  `Γ ℚ → (ℚ̄ ≃+* ℚ̄)`), PROVEN trivial on the fixing subgroup of ℚ(μ_ℓ)
  (`cyclotomicCharacterModL_eq_one`) and PROVEN continuous into the
  discrete `ZMod ℓ` (`continuous_cyclotomicCharacterModL`, Krull-open
  kernel + coset covering). Two new faithful sorry nodes stated:
  ✗ `cyclotomicCharacterModL_globalFrob` (χ̄(Frob_q) = q for q ≠ ℓ) and
  ✗ `not_isIrreducible_of_charpoly_eq` (Brauer–Nesbitt, 2-dim mod-ℓ
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
  DERIVED** — `not_isIrreducible_of_charFrob_eq` is now PROVEN in
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
- 2026-07-16 (session 4): **Tate-curve/reduction batch vendored, ZERO
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
- 2026-07-16 (session 4, cont.): **QuadraticTwists closure vendored,
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
- 2026-07-16 (session 4, cont.): **TateCurve.lean vendored with the
  sorry-d data reformulated existentially** — the fully proven upstream
  material (Tate curve series `tateA₄`/`tateA₆`/`tateCurve` with their
  `evalInt` identities, the valuation lemmas `valuation_Δ_lt_one`,
  `valuation_c₄_eq_one`, `valuation_j_eq`, `one_lt_valuation_j`, the
  Tate parameter `q`/`qUnit` with `q_ne_zero`/`valuation_q_lt_one`,
  base-change functoriality `tateCurve_baseChange`,
  `tateParameter_map`, `q_baseChange`, and the reduction-preserving
  instances) is vendored verbatim. The upstream sorry-d DATA
  (`tateCurveEquiv`, `tateEquiv`, `tateEquivSepClosure`, `tatePoint`)
  and its satellite lemmas are replaced by TWO honest Prop nodes:
  ✗ `exists_variableChange_tateCurve` (Tate's theorem ATAEC V.5.3:
  `E ≅ E_{q(E)}` by a variable change) and
  ✗ `exists_tateEquivSepClosure` (a Galois-equivariant group iso
  `Ωˣ/qᶻ ≅ E(Ω)` over a separable closure — an existential Prop, since
  the iso is canonical only up to sign). The upstream import of the
  sorry-d WeilPairing data file is dropped; `weilPairing_tatePoint`
  (sign coherence between the two packages) is NOT vendored — if a
  consumer appears it must be stated as a joint existential. Frontier:
  19 (17 + the 2 new Tate nodes). Next: decompose
  `torsion_isTameAtTwo` against `exists_tateEquivSepClosure` +
  `exists_quadraticTwist_hasSplitMultiplicativeReduction`.
- 2026-07-16 (session 4, cont.): **`isCoprime_Φ_ΨSq` DERIVED from
  `resultant_Φ_ΨSq`** — mathlib's
  `Polynomial.exists_mul_add_mul_eq_C_resultant` (the resultant lies in
  the ideal generated by the two polynomials, via the adjugate of the
  Sylvester map) with the degree bounds `natDegree_Φ_le` /
  `natDegree_ΨSq_le` gives `Φ n * p + ΨSq n * q = C (resultant)`; the
  resultant node evaluates this to `±Δ^k`, a unit when `Δ` is, and
  scaling the Bézout identity by its inverse closes `IsCoprime`.
  Frontier: 18.
- 2026-07-16 (session 4, cont.): **`torsion_isUnramified` DECOMPOSED
  by reduction type** — the node is now DERIVED from two new faithful
  nodes via the case split on `q ∣ abc`:
  ✗ `torsion_isUnramified_of_good` (good reduction at `q ∤ abc`, to be
  closed against the vendored NOS node) and
  ✗ `torsion_isUnramified_of_multiplicative` (`q ∣ abc`: multiplicative
  reduction, `p ∣ v_q(j)`, quadratic twist to split reduction, Tate
  uniformization). Each new node isolates one mechanism; the vendored
  infrastructure for both (GoodReduction.lean;
  SplitMultiplicativeReduction.lean + TateCurve.lean) is in place.
  Frontier: 19.
- 2026-07-16 (session 4, cont.): **`torsion_isFlat` DECOMPOSED by
  reduction type** — same pattern as `torsion_isUnramified`: DERIVED
  from ✗ `torsion_isFlat_of_good` (`p ∤ abc`: Néron-model torsion is
  finite flat, to be closed against the vendored
  `torsion_flat_of_good_reduction`) and
  ✗ `torsion_isFlat_of_multiplicative` (`p ∣ abc`: `p ∣ v_p(j)` makes
  the Tate-curve extension peu ramifiée, which prolongs finite-flatly)
  via the case split on `p ∣ abc`. Frontier: 20.
- 2026-07-16 (session 4, cont.): **`torsion_isUnramified_of_good`
  DECOMPOSED into arithmetic + glue** — new own-work file
  `FreyCurve/Semistable.lean`: the node is DERIVED from
  ✗ `freyCurve_hasGoodReduction_of_not_dvd` (the arithmetic: at odd
  `q ∤ abc` the Frey equation is `q`-integral with `q`-unit
  discriminant, so minimal with good reduction over
  `Localization.AtPrime v_q`) and
  ✗ `isUnramifiedAt_of_hasGoodReduction` (the local-global glue:
  good reduction at `q ≠ p` ⟹ `IsUnramifiedAt q`, to be closed against
  the vendored NOS node). The `ℤ_(q)`-as-DVR-with-fraction-field-ℚ
  instance package (Algebra/IsScalarTower/IsFractionRing/
  IsDiscreteValuationRing for `Localization.AtPrime v.asIdeal`) is
  PROVEN as public named instances (mathlib has the lemmas but no
  instances; note `IsDedekindDomainDvr.is_dvr_at_nonzero_prime` needed
  explicit `@`-application — instance-synthesis stalls on its
  `IsDomain (𝓞 ℚ)` argument even though direct synthesis succeeds).
  Frontier: 21.
- 2026-07-16 (session 4, cont.): **`freyCurve_hasGoodReduction_of_not_dvd`
  PROVEN** — the good-reduction arithmetic node is closed:
  `q`-integrality via the integral model (`freyCurveInt` and
  `FreyCurve.map`, each coefficient an integer, lifted through
  `map_intCast`); the discriminant `(abc)^{2p}/2⁸` is exhibited as the
  image of the explicit unit `(abc)^{2p}·(2⁸)⁻¹` of `ℤ_(q)` (both
  factors prime to `q`, inverted via `IsLocalization.AtPrime.
  isUnit_to_map_iff` and the new PROVEN bridge lemmas
  `intCast_mem_toHeightOneSpectrumRingOfIntegersRat_iff` and
  `isUnit_intCast_localizationAtPrime`), so the adic valuation of Δ is
  `1` by `mker_valuation_eq_isUnitSubmonoid`; minimality follows since
  valuation `1` is the maximum over integral models (the
  `valuation_Δ_aux` subtype bound). Frontier: 20.
- 2026-07-16 (session 4, cont.): **`torsion_isFlat_of_good` DERIVED** —
  the PROVEN arithmetic node applies verbatim at `q := p` (`p ≠ 2`
  since `p ≥ 5`), and a new glue node
  ✗ `isFlatAt_of_hasGoodReduction` (good reduction at `p` ⟹
  `IsFlatAt p`, to be closed against the vendored
  `torsion_flat_of_good_reduction` Hopf-package node) completes the
  derivation. Frontier: 20 (one closed, one opened).
- 2026-07-16 (session 4, cont.): **multiplicative arithmetic PROVEN;
  both multiplicative consumers DERIVED** —
  `freyCurve_hasMultiplicativeReduction_of_dvd` is PROVEN (integrality;
  `c₄ = c^{2p} - (ab)^p` prime to `q` by the pairwise-coprimality Xor;
  minimality by the vendored unit-`c₄` Kraus–Laska criterion
  `isMinimal_of_valuation_c₄_eq_one`; `v(Δ) < 1` via
  `valuation_lt_one_iff_mem` since `abc` lands in the maximal ideal).
  `torsion_isUnramified_of_multiplicative` and
  `torsion_isFlat_of_multiplicative` are DERIVED from it (+ the proven
  `j_valuation_of_bad_prime`) through two new glue nodes:
  ✗ `isUnramifiedAt_of_hasMultiplicativeReduction` (Tate glue at
  `q ≠ p`) and ✗ `isFlatAt_of_hasMultiplicativeReduction`
  (peu-ramifiée glue at `p`). All four FreyConditions reduction-type
  cases now rest exclusively on local-global glue nodes; the Frey-curve
  semistability arithmetic is complete. Frontier: 20.
- 2026-07-16 (session 4, cont.): **Frey multiplicative reduction AT 2
  PROVEN; `torsion_isTameAtTwo` DERIVED** —
  `freyCurve_hasMultiplicativeReduction_at_two` is PROVEN (this is
  where the Frey model's defining congruences `a ≡ 3 mod 4`, `b ≡ 0
  mod 2` are consumed: they force `c` odd, so `c₄` is odd and
  `v(c₄) = 1`, while `Δ = 2^{2p-8}(ab'c)^{2p}` is in the maximal ideal
  as `2p > 8`); `torsion_isTameAtTwo` is DERIVED from it through the
  new glue node ✗ `isTameAtTwo_of_hasMultiplicativeReduction` (stated
  for a general elliptic curve over ℚ — the Tate/quadratic-twist glue
  at 2). ALL FOUR conditions of `IsHardlyRamified` for the Frey curve
  now rest exclusively on generic local-global glue nodes; every
  Frey-specific computation is sorry-free. Frontier: 20.
- 2026-07-16 (session 4, cont.): **Serre's reducible-case node
  DECOMPOSED; the CRT assembly PROVEN** —
  `exists_torsion_embedding_of_not_isIrreducible` is now DERIVED from
  ✗ `exists_two_torsion_and_p_point_of_not_isIrreducible` (Serre's
  core: reducibility ⟹ some curve has full rational 2-torsion AND a
  rational point of order exactly p — the Minkowski/Vélu content) and
  ✓ `embedding_assembly` (PROVEN: injective (ℤ/2)² + element of order
  p assemble into injective ℤ/2 × ℤ/2p, via `ZMod.chineseRemainder`,
  `ZMod.lift` for the p-part, and the coprime-annihilator separation
  `p•u = u` for 2-torsion u with p odd). Frontier: 20 (one closed, one
  opened; the remaining Serre node no longer contains the group
  theory).
- 2026-07-16 (session 4, cont.): **Frey full rational 2-torsion PROVEN;
  Serre core split by character case** —
  `freyCurve_two_torsion_embedding` is PROVEN: the transformed Frey
  model has visible rational 2-torsion at `(0,0)` and `(aᵖ/4, −aᵖ/8)`
  (equation checks by `field_simp`/`ring`; nonsingularity from
  `equation_iff_nonsingular` since the curve is elliptic; order 2 via
  the negation formula `negY`; the two points differ in
  `x`-coordinate), assembled into an injective `(ℤ/2)² →+ E(ℚ)`.
  `exists_two_torsion_and_p_point_of_not_isIrreducible` is now DERIVED
  from the new disjunction node ✗ `exists_p_point_of_not_isIrreducible`
  (χ₁ = 1: p-point on the Frey curve itself, 2-torsion supplied by the
  proven lemma; χ₂ = 1: the full package on the Vélu quotient). The
  remaining Serre node isolates exactly Minkowski + Vélu. Frontier: 20.
- 2026-07-16 (session 4, cont.): **Minkowski EXTRACTED as a faithful
  node** — `exists_p_point_of_not_isIrreducible` is now DERIVED from
  ✗ `minkowski_character_trivial` (a mod-`p` character of G_ℚ with open
  kernel unramified at every finite place — stated with
  `localInertiaGroup` and the restriction along
  `Field.absoluteGaloisGroup.map` — is trivial; to be closed against
  mathlib's `NumberField.abs_discr_gt_one` via the fixed field of the
  kernel) and ✗ `exists_p_point_of_not_isIrreducible_of_minkowski`
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
  DERIVED (the kernel of an everywhere-unramified character is an open
  normal subgroup containing every inertia image, via
  `Subgroup.map_le_iff_le_comap`); the sorry now lives in
  ✗ `open_normal_subgroup_eq_top_of_inertia_le`, a pure
  Galois/number-theoretic statement with no characters or `ZMod p`
  in sight — exactly the statement the mathlib discriminant route
  closes. Frontier: 21 (sorry relocated, interface simplified).
- 2026-07-16 (session 4, cont.): **OddAbsIrred vendored, ZERO
  sorries** — `KnownIn1980s/RepresentationTheory/OddAbsIrred.lean` +
  `Slop/RepresentationTheory/OddAbsIrredSlop.lean` (495 lines, fully
  proven): for a finite-dimensional representation with some `g` having
  a one-dimensional fixed space (e.g. complex conjugation on an odd
  2-dim Galois rep), irreducible ⟺ absolutely irreducible
  (`OddRep.isIrreducible_iff_isAbsolutelyIrreducible`). Wired into the
  root. Mapped feed for the B6 chain / `mod_three` (together with the
  still-unvendored `Slop/PGL2` Dickson classification). Frontier
  unchanged: 21.
- 2026-07-16 (session 4, cont.): **Dickson classification vendored,
  ZERO sorries (13 files, ~11.5k lines)** — the full
  `Slop/PGL2/FiniteSubgroups` development plus
  `KnownIn1980s/PGL2/Defs.lean` with the classification theorems
  (`Dickson.classification_tame`: a nontrivial finite subgroup of
  `PGL₂(𝔽̄_p)` of order prime to `p` is cyclic, dihedral, A₄, S₄ or A₅;
  `Dickson.classification_wild`: order divisible by `p` gives
  elementary-abelian-by-cyclic, PSL₂/PGL₂ of a subfield, or A₅ at
  `p = 3`). VENDORING CHANGE: upstream leaves the Defs statements
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
  PROVEN** (unconditional) — for distinct primes `q ≠ p`, `p` is
  nonzero in the residue field of `ℤ_(q)` (`p` is a unit of the
  localization; units have nonzero residue). This pre-discharges the
  `NeZero (n : ResidueField R)` hypothesis of the vendored NOS and
  finite-flat nodes for when the good-reduction glue nodes are closed
  against them.
- 2026-07-16 (session 4 close): **Tate torsion-membership lemmas
  PROVEN** — `WeierstrassCurve.mem_torsionBy_of_mem_rootsOfUnity` and
  `mem_torsionBy_of_pow_eq` (in `TateCurve.lean`): under ANY witness
  `e : Ωˣ/qᶻ ≃+ E(Ω)` of `exists_tateEquivSepClosure`, `N`-th roots of
  unity and `N`-th roots of the Tate parameter map to `N`-torsion
  points (formal: `N•[u] = [u^N]` and the class of `q` is zero).
  These serve the multiplicative/tame glue nodes, which analyze `E[p]`
  through the uniformization's torsion.
