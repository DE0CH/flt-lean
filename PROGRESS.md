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

## Tree (✓ = proven here or in mathlib, ✗ = sorry, ○ = in progress)

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
      - ✗ `FreyPackage.mazur` (`Fermat/FLT/FreyCurve/Mazur.lean`) — the mod-p
        rep of the Frey curve is irreducible (Mazur + Serre §4.1); plain
        `sorry`, an open node like any other.
      - ✗ `FreyPackage.galoisRep_not_irreducible` (B4, `Fermat/PrimeFive.lean`)
        — Wiles modularity + Ribet level lowering + no weight-2 level-2 cusp
        forms. This is also the current frontier of the FLT project itself
        (their B5/B6, hardly-ramified route, not yet stated in Lean there).
      - Supporting sorries in vendored infrastructure
        (`Fermat/FLT/EllipticCurve/Torsion.lean`):
        `n_torsion_finite`, `n_torsion_card`, `group_theory_lemma`,
        `Module.Finite` instance, `galoisRepresentation` DistribMulAction
        fields ("should all be easy" per FLT project), and — nota bene —
        `WeierstrassCurve.galoisRep` itself, which is **sorry-d DATA** (the
        continuous Galois representation on p-torsion); the FLT project has
        it sorry-d too. Statements about sorry-d data are about an
        unspecified representation; this must eventually be filled with the
        real construction for B4/Mazur to mean what they should.
      - `Fermat/FLT/GaloisRepresentation/HardlyRamified/Frey.lean`: 2 sorries
        (the Frey curve's rep is hardly ramified — Serre §4.1).

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
