# HANDOFF: FLT formalization — context for the successor agent

You are taking over a long-running autonomous project (last updated
2026-07-16, session 4). Read this file plus `PROGRESS.md` (same directory)
fully before doing anything. `PROGRESS.md` is the single source of truth
for the tree state; this file covers mission, policies, and mechanics.

## The mission (from Deyao)

Formalize **Fermat's Last Theorem completely in Lean 4** in this `fermat/`
project. Deliberately maximalist; expected to take weeks of continuous
autonomous work. Work autonomously; commit and push frequently.

Method — resolve a dependency tree top-down:
1. The top-level theorem is proven; every gap is an explicit `sorry`-d
   theorem (the open nodes). Walk the tree: pick a node, decompose it into
   further stated-and-sorried nodes or prove it outright.
2. After every change: `lake build`, axiom audit, commit/push, update
   `PROGRESS.md` (tree + log), re-check the frontier, continue.

## THE LOOP (Deyao, non-negotiable)

- **One exit condition**: `lake build` passes the sorry gate AND
  `grep -rn "sorry" Fermat --include="*.lean"` finds zero proof-position
  sorries. Until then the loop runs forever; continue every iteration
  regardless of how stuck the previous one was.
- **No giving-up prose.** Incapability must surface as repeatedly failed
  attempts (compiler errors, failing builds) inside a loop that cannot
  exit — never as "I can't continue / here's what's missing" text. Deyao
  terminates externally; that is his prerogative, not the program's.
- **Enforcement mechanisms** (all live; see CLAUDE.md for details):
  - *Stop hook*: `.claude/check-sorries.py` (registered in
    `.claude/settings.json`) vetoes every attempt to end the turn while
    the exit condition is unmet, feeding the next open nodes back.
    `CLAUDE_CODE_STOP_HOOK_BLOCK_CAP=1000`.
  - *Sorry gate*: root `Fermat.lean` ends with `#assert_no_sorry
    fermat_last_theorem` (`Fermat/SorryGate.lean`) — `lake build` FAILS
    with `SORRY GATE FAILED` while nodes remain and also enforces the
    axiom invariant. A gate failure is the EXPECTED build outcome; any
    other error is a genuine defect.
  - *warningAsError*: the lakefile makes every warning a hard error; each
    deliberate sorry node opts out with `set_option warn.sorry false in`
    placed ABOVE its docstring. A sorry without the opt-out fails the
    build by design.

## Non-negotiable policies (Deyao)

- **No citation-terminal nodes.** The FLT project's `knownin1980s` axiom
  is BANNED. A node closes only when Lean compiles its proof. Scope
  ballooning is accepted; do not relitigate.
- **No deferral**: nothing is "below" anything; every sorry is an active
  frontier node.
- **Never introduce an `axiom`.** Axiom invariant: every declaration uses
  at most `[propext, Classical.choice, Quot.sound, sorryAx]` (the gate
  checks this at the root).
- **`git push --force` banned** in all forms. Ordinary commit/push
  expected every iteration.
- **Multiple agents share this repo.** This worktree (`~/cs/flt-worktree`,
  branch `flt-formalization`) is YOURS; other worktrees/main checkout
  belong to other agents. tmux session names: pick unique ones (a session
  named `hooktest` belongs to the W* agent — do not touch).
- **NEVER build Lean under `~/Documents`** (iCloud eviction hazard);
  `~/cs` is safe.

## Current state — read PROGRESS.md for the authoritative tree

**Session 5 FINAL STATE (2026-07-17, frontier 19):**
0. **THE SHARED FLAT TRANSPORT IS SORRY-FREE** (2026-07-17):
   `GaloisRep.isFlatAt_of_dvr_package` (two-ideal split over a field
   `A` + `HasFlatProlongationAt.of_addEquiv`),
   `hasFlatProlongationAt_of_hopf_package` (general-`K` core:
   `G := 𝒪ᵥ ⊗[R] H`, `dvrPointsEquiv` = three `liftEquiv`s +
   `algHomEquivOfFinite`, convolution layers vs mathlib `WithConv`,
   equivariance via `lift_map`), and the `ℤ_(q)`-instantiation all
   audit to standard axioms (see PROGRESS.md 2026-07-17 for the four
   recorded gotchas: postponed ∃-instance metavars, structure-literal
   `?_` binders, the `DivisionRing.toRatAlgebra` pin at `ℚ`, the
   `Algebra`+`Bialgebra` SMul diamond). Both `IsFlatAt` glue nodes
   now rest ONLY on the content leaves.
1. **THE ENTIRE MINKOWSKI BRANCH IS PROVEN UNCONDITIONALLY** — the
   local node (Neukirch II.9.11) was fully formalized: finite-level
   Hilbert `|I| = e` counting (`card_inertia_finite_level`,
   `card_inertia_intermediate`, the counting combiner), finite-level
   inertia surjectivity, the profinite compactness lifting, and the
   reification/e-transport assembly. `minkowski_character_trivial`,
   `open_normal_subgroup_eq_top_of_inertia_le`, the inertia
   dictionary, and the surjectivity leaf all audit to
   `[propext, Classical.choice, Quot.sound]`.
2. **ALL FIVE local-global glue nodes are DERIVED** onto content
   leaves + shared transports: the two `IsUnramifiedAt` glues via the
   PROVEN embedded-valuation-subring machinery
   (`embeddedValuationSubring` + `h𝒪`-compatibility + the
   `inertiaSubgroup` spelling bridge, all in
   `LocalInertiaFixedField.lean`) against the vendored NOS leaf resp.
   the new Tate leaf `torsion_unramified_of_multiplicative_reduction`;
   the two `IsFlatAt` glues via the new SHARED transport node
   `GaloisRep.isFlatAt_of_dvr_package` (`FlatProlongation.lean`;
   design fully de-risked in PROGRESS.md — Hopf base change
   scratch-verified, `localizationToAdicCompletionIntegers` and the
   subsingleton case PROVEN) against the vendored flat leaf resp. the
   new peu-ramifiée leaf `torsion_flat_of_multiplicative_reduction`.
3. Remaining frontier (19): the four elliptic content leaves above +
   `mazur_classification`,
   `exists_p_point_of_not_isIrreducible_of_minkowski`,
   `mod_three_reducible`, `mod_three_of_stable_line`, `three_adic`,
   `exists_hardlyRamifiedLift`, `mem_isCompatible`,
   `exists_frobenius_conj_mem_coset`, `exists_weilPairing`,
   `smul_surjective`, `prime_torsion_card`,
   `exists_variableChange_tateCurve`, `exists_tateEquivSepClosure`,
   `resultant_Φ_ΨSq`, `torsion_unramified_of_good_reduction`,
   `torsion_flat_of_good_reduction`.

**Session 5 (2026-07-16) headline:** the Minkowski surjectivity leaf
`exists_prime_over_inertia_eq_bot_of_le_fixingSubgroup` is DERIVED (the
valuation route: embed `L` into `M = ℚ_q(ι L)`, the local node makes
`q` a uniformizer of `𝒪_M`, the comap prime has `e = 1`, and
`#I = e` closes; NO decomposition groups, NO henselian lifting). The
entire Minkowski branch now rests on ONE local node,
`maximalIdeal_map_eq_of_le_fixedField_localInertiaGroup`
(`Deformations/RepresentationTheory/LocalInertiaFixedField.lean`): a
finite subextension `M/Kᵥ` of `Kᵥᵃˡᵍ` fixed pointwise by
`localInertiaGroup v` has `e(M/Kᵥ) = 1`. Around it, PROVEN
unconditionally: `card_inertia_finite_level` (`|I| = e` at finite
Galois levels over `𝒪ᵥ`), `restrictNormalHom_mem_inertia_of_mem_localInertiaGroup`
(restriction of local inertia into finite-level inertia),
`isDiscreteValuationRing_integralClosure` (`𝒪_N` is a DVR),
`maximalIdeal_map_eq_of_ramificationIdx_eq_one` (`e = 1 ⟹` ideal
equality), `adicCompletionIntegers_ne_top`, plus the instance layer
(IsIntegralClosure for the synonym, SMulDistribClass, two restricted
towers, LiesOver of `𝔪_N`). CRITICAL LEAN GOTCHA discovered:
`set_option backward.isDefEq.respectTransparency false in` fixes the
otherwise-unsynthesizable `Module.Free/Flat` instances over
`IntegralClosure 𝒪ᵥ ↥N` (divergent embedded instance arguments) — any
lemma synthesizing module-structure classes over the synonym likely
needs it. Remaining for the local node (full design in PROGRESS.md
session-5 log): generalize the `FiniteLevel` section to arbitrary
finite `E/Kᵥ`, declare the canonical
`Algebra (IC 𝒪ᵥ ↥M') (IC 𝒪ᵥ E)` instance for
`M' : IntermediateField Kᵥ E` (codRestrict, NO `≤`-hypothesis needed),
prove the M-based counting
(`e(E/Kᵥ) = |I(𝔪_E/Gal(E/Kᵥ))| ≤ |I(𝔪_E/Gal(E/M'))| = e(E/M')` via
`fixingSubgroupEquiv`, then `ramificationIdx'_algebra_tower` forces
`e(M') = 1`), the compactness lifting of finite-level inertia to
`localInertiaGroup` (Γ profinite, `localInertiaGroup` closed via
locally-constant evaluation, finite-to-finite surjectivity by the same
counting), and the final assembly. mathlib's
`stabilizerHom_surjective` is `[Finite G]`-only — no profinite
shortcut.

Session 4 (2026-07-16) closed with **22 leaf sorry nodes** (all Props;
grep for the live list — PROGRESS.md's canonical enumeration plus the
late-session splits: the Minkowski transport is now
[`exists_prime_over_inertia_eq_bot_of_le_fixingSubgroup`, surjectivity]
with conjugacy propagation PROVEN, and `mod_three` is now
[`mod_three_reducible`, Dickson/discriminant] +
[`mod_three_of_stable_line`, quotient character] with the composition
derived). Session-4 headlines: the entire Tate-curve /
QuadraticTwists / reduction infrastructure is vendored SORRY-FREE (28
files; TateCurve.lean's sorry-d data reformulated as two existential
Prop nodes); the Frey curve's ENTIRE semistability arithmetic is PROVEN
(good reduction at q ∤ abc, multiplicative reduction at odd q ∣ abc AND
at 2 — the last consuming the model's defining congruences); all four
IsHardlyRamified conditions and both Mazur-side Serre steps now rest
exclusively on GENERIC glue nodes; Frey full rational 2-torsion PROVEN;
isCoprime_Φ_ΨSq derived from the resultant node; Minkowski extracted
down to its character-free subgroup form.

The 21 leaves, grouped:
- **Five local-global glue nodes** (`FreyCurve/Semistable.lean` +
  `FreyConditions.lean`): isUnramifiedAt/isFlatAt at good primes (close
  against the vendored NOS/Flat nodes), isUnramifiedAt/isFlatAt at
  multiplicative primes and isTameAtTwo (close against the vendored
  quadratic-twist theorem + `exists_tateEquivSepClosure`).
  **UNIFICATION (session-4 close)**: `GaloisRep.ker_map` is `rfl`, so
  each glue node's `IsUnramifiedAt` conclusion is EXACTLY the Minkowski
  transport hypothesis with `ρ.ker` in place of `L.fixingSubgroup` —
  the TWO `IsUnramifiedAt` glue nodes and the Minkowski surjectivity
  leaf consume ONE embedding-prime transport family directly (the
  flat/tame glue nodes have additional content — flat prolongation
  resp. the quotient-character package — with the transport as an
  ingredient, not the whole). Build that transport once, in the
  generality serving the three direct consumers (see the session-4 reconnaissance in
  PROGRESS.md for the full verified chain around it).
- **Two vendored reduction-theory leaves**: `torsion_unramified_of_good_reduction`
  (NOS), `torsion_flat_of_good_reduction` (Hopf package), plus
  `resultant_Φ_ΨSq`.
- **Two Tate existentials**: `exists_variableChange_tateCurve`,
  `exists_tateEquivSepClosure`.
- **Mazur branch**: `mazur_classification` (Mazur's theorem),
  `exists_p_point_of_not_isIrreducible_of_minkowski` (Serre core —
  remaining content: Vélu quotients + character bookkeeping), and
  `isUnramifiedAt_of_inertia_le_fixingSubgroup` (**THE inertia
  dictionary — the highest-leverage node**: the Minkowski subgroup
  form was DERIVED from it late in session 4 via mathlib's
  discriminant theory, and the SAME dictionary is what all five glue
  nodes need; closing it unlocks six nodes' structure. Its endpoints
  are reduced to definitional membership — see the session-4
  reconnaissance).
- **Torsion/pairing**: `smul_surjective`, `prime_torsion_card` (blocked
  on isogeny theory or a division-polynomial↔[n] bridge, neither in
  mathlib at our pin), `exists_weilPairing`.
- **Galois-representation deep end**: `exists_frobenius_conj_mem_coset`
  (finite-level Chebotarev), B6a `exists_hardlyRamifiedLift`, B6b
  `mem_isCompatible`, B6c `three_adic`, and the `mod_three` pair
  `mod_three_reducible` + `mod_three_of_stable_line` (their inputs —
  the `Slop/PGL2` Dickson classification and `OddAbsIrred` — are NOW
  VENDORED sorry-free, and the second node reuses the derived
  Minkowski machinery).

## Workflow

- Build: `cd ~/cs/flt-worktree/fermat && lake build` — EXPECT the sorry
  gate error; anything else is a defect.
- Axiom audit: scratch file importing `Fermat.Basic` + the touched leaf
  modules (NEVER root `Fermat` — its olean does not exist while the gate
  fails), `#print axioms <decls>`, run `lake env lean <file>`.
- Lean module-system gotchas (hard-won):
  - In `module` files, some legacy mathlib instances (e.g.
    `AlgebraicClosure.isAlgebraic`) only synthesize under
    `set_option backward.isDefEq.respectTransparency false in`.
  - `set_option ... in` AND `omit [...] in` lines go ABOVE a
    declaration's docstring.
  - Non-public imports are proof-only and NOT re-exported; each module
    needs its own imports for statement-level names AND instances.
  - Auto-generated instance names collide across vendored files — name
    local instances explicitly.
  - `set`-bound local abbreviations hide instances; inline the types
    (e.g. `IsLocalRing.ResidueField R` with `set R := Localization...`
    fails instance resolution; write the localization type out).
  - `hq.foo` dot-notation on `hq : Nat.Prime q` resolves via the
    `Irreducible` namespace ("Invalid field" error) when the module
    DEFINING `Nat.Prime.foo` is not imported — fix the import, not the
    name.
  - Instance-synthesis can stall on an argument (e.g. `IsDomain (𝓞 ℚ)`
    inside `IsDedekindDomainDvr.is_dvr_at_nonzero_prime`) even when
    direct synthesis of the same instance succeeds — pass it explicitly
    with `@` and a `haveI`-bound witness.
  - `zsh` does not word-split unquoted `$var` — a for-loop over a
    space-separated list needs the literal list in the `for` line (a
    quoted-variable loop creates ONE bogus space-containing path).
  - Vendored upstream files that import a Defs file you are inlining
    proofs into create build CYCLES — split the shared definitions into
    a `Basic.lean` (as done for `PGL2/Basic.lean`).
- Vendoring from `~/cs/FLT` (reference clone, never build there): keep
  Apache headers, rewrite `FLT.` → `Fermat.FLT.`, replace their
  assumption mechanisms with tracked sorry nodes, mark VENDORING CHANGEs.
- Sources: `~/cs/FLT` (git pull occasionally; their newer layers are a
  map), web search, SOLO Oxford via browser automation (captcha ⇒
  abandon), Anna's Archive MCP (retry same md5 with different
  domain_index on TLS errors; never disable cert verification).
- Ping Deyao by push notification only for blocked-on-user decisions or
  milestone completions.
