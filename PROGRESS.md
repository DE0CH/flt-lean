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
        - ✗ `FreyPackage.exists_torsion_embedding_of_not_isIrreducible` —
          if the rep is reducible, some elliptic curve over ℚ (the Frey
          curve or its quotient by the rational order-p subgroup cut out by
          the stable line) has rational points containing ℤ/2 × ℤ/2p:
          semistability + Minkowski force a trivial character (rational
          p-point on E or E/C), and full 2-torsion is rational on both
          (visible Weierstrass form resp. odd-degree rational isogeny).
          Folds the quotient-curve construction into an existential:
          - □ quotients of elliptic curves by finite rational subgroups
            (Vélu) — needed to split this node faithfully.
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
          - ✗ `FreyCurve.torsion_det` — det ρ̄ = mod-p cyclotomic
            character (the Weil pairing; not yet in mathlib).
          - ✗ `FreyCurve.torsion_isUnramified` — unramified outside
            {2, p}: Néron–Ogg–Shafarevich at good primes; Tate curve +
            p ∣ v_q(j) (`j_valuation_of_bad_prime`, proven) at the
            multiplicative primes.
          - ✗ `FreyCurve.torsion_isFlat` — flat at p (finite flat group
            scheme over ℤ_p; Néron model / Tate curve at p).
          - ✗ `FreyCurve.torsion_isTameAtTwo` — at 2: rank-1 quotient
            with unramified character squaring to 1 (multiplicative
            reduction at 2, Tate uniformization, quadratic twist).
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
          - ✗ **B6bc** `residual_charFrob_eq` — the residual Frobenius
            charpolys of a liftable rep are those of `1 ⊕ χ̄`
            (`X² − (q+1)X + q`). Folds B6b (spread out to a weakly
            compatible family over a number field's completions) and B6c
            (3-adic hardly ramified ⇒ extension of trivial by cyclotomic);
            a later layer must split it into faithful B6b/B6c statements.
          - ✗ `not_isIrreducible_of_charFrob_eq` — Chebotarev + Brauer–
            Nesbitt: Frobenius charpolys of `1 ⊕ χ̄` away from `{2,3,ℓ}`
            force reducibility.
      - Supporting sorries in vendored infrastructure
        (`Fermat/FLT/EllipticCurve/Torsion.lean`):
        - ✓ `n_torsion_finite` — now DERIVED (2026-07-16) in
          `TorsionFinite.lean` (own work) from two explicit polynomial
          nodes: a nonzero torsion point's abscissa is a root of the
          division polynomial `ΨSq n` (✗
          `TorsionFinite.eval_ΨSq_eq_zero_of_smul_eq_zero` — the
          multiplication-by-`n` formulas, D. Angdinata's thesis
          material), and ✗ `TorsionFinite.ΨSq_ne_zero_of_charDvd`
          (nonvanishing when char ∣ n; the `(n : k) ≠ 0` case is mathlib's
          `ΨSq_ne_zero`). Given these, finiteness is elementary: finitely
          many abscissae, ≤ 2 ordinates each (monic quadratic).
        - ✗ `n_torsion_card` (= n² over sep. closed fields, `(n : k) ≠ 0`) —
          needs the full division-polynomial biconditional + multiplicity
          analysis.
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
