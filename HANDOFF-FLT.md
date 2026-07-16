# HANDOFF: FLT formalization — context for the successor agent

You are taking over a long-running autonomous project (last updated
2026-07-16, session 3). Read this file plus `PROGRESS.md` (same directory)
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

Everything through the boss-theorem spine is DERIVED down to ~17 leaf
sorry nodes (all Props; grep for the live list). Highlights of what is
already proven sorry-free: group_theory_lemma / torsion counting; the
galoisRep construction with continuity; Mazur weak torsion bound from the
classification; the four IsHardlyRamified conditions assembled; B5 → B6
chain assembled; B6bc from B6b + glue; the Chebotarev–Brauer–Nesbitt node
fully derived from density + BN + Frobenius-value (with proven bridges:
mod-ℓ cyclotomic character + continuity, End-discreteness,
place↔prime, monic-quadratic ext); torsion_det from the Weil pairing
node + proven determinant linear algebra.

The remaining leaves are deep: Mazur classification, Serre §4.1
reducible-case, NOS/Tate unramifiedness, flatness at p, tameness at 2,
B6a (deformation lifting), B6b (compatible families), the glue
bookkeeping, B6c/mod_three, Chebotarev density, Brauer–Nesbitt,
χ̄(Frob_q) = q, Weil pairing existence, division-polynomial nodes
(n_torsion_card, eval_ΨSq, ΨSq_ne_zero_of_charDvd).

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
  - `set_option ... in` lines go ABOVE a declaration's docstring.
  - Non-public imports are proof-only and NOT re-exported; each module
    needs its own imports for statement-level names AND instances.
  - Auto-generated instance names collide across vendored files — name
    local instances explicitly.
  - `set`-bound local abbreviations hide instances; inline the types.
- Vendoring from `~/cs/FLT` (reference clone, never build there): keep
  Apache headers, rewrite `FLT.` → `Fermat.FLT.`, replace their
  assumption mechanisms with tracked sorry nodes, mark VENDORING CHANGEs.
- Sources: `~/cs/FLT` (git pull occasionally; their newer layers are a
  map), web search, SOLO Oxford via browser automation (captcha ⇒
  abandon), Anna's Archive MCP (retry same md5 with different
  domain_index on TLS errors; never disable cert verification).
- Ping Deyao by push notification only for blocked-on-user decisions or
  milestone completions.
