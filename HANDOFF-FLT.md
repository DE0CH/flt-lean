# HANDOFF: FLT formalization — context for the successor agent

You are taking over a long-running autonomous project from a previous Claude
session (2026-07-16). Read this file plus `PROGRESS.md` (same directory)
fully before doing anything.

## The mission (from Deyao)

Formalize **Fermat's Last Theorem completely in Lean 4** in this `fermat/`
project. This is an enormous, deliberately maximalist academic project — it
is expected to take **weeks of continuous autonomous work**. Do not stop
until it is done or Deyao stops you. Work autonomously; commit and push
frequently.

Method — treat it as resolving a software dependency tree:
1. The top-level theorem is proven; every gap is an explicit `sorry`-d
   theorem (the "open nodes").
2. Walk the tree: pick an open node, decompose it into further statements
   (write them, `sorry` their proofs) or prove it outright.
3. After every change: `lake build` must succeed, and check axioms with
   `#print axioms <decl>` — every declaration must use at most
   `[propext, Classical.choice, Quot.sound, sorryAx]`. **Never introduce an
   `axiom`.** Never let a statement silently change meaning.

## Non-negotiable policies (Deyao, verbatim intent)

- **No citation-terminal nodes.** The FLT project's `knownin1980s` axiom
  ("an expert could deduce this from pre-1990 literature") is BANNED. No
  node may be closed by appeal to expert knowledge or literature. A node is
  closed only when Lean compiles its proof. Scope ballooning is accepted —
  it is Deyao's explicit aesthetic/academic choice; do not relitigate it.
  Rationale: the trust boundary must be the Lean kernel + the visible sorry
  list, never a human assertion.
- **`git push --force` is banned** in all forms. Ordinary commits/pushes are
  fine and expected.
- **Multiple agents work on this repo.** This worktree
  (`~/cs/flt-worktree`, branch `flt-formalization`) is YOURS; the main
  checkout `~/cs/dissertation` and other worktrees belong to other agents —
  do not touch them.
- **NEVER build Lean (or put any `.lake`) under `~/Documents`** — it is
  iCloud-synced; a 7.2G/200k-file build tree there caused a catastrophic
  eviction of the old repo copy on 2026-07-16 (that's why the repo was
  re-cloned to `~/cs/dissertation`). `~/cs` is safe (not iCloud).

## Current state (branch flt-formalization @ d7a0162, pushed)

- `Fermat/Basic.lean` — `fermat_last_theorem : FermatLastTheorem` PROVEN
  from mathlib (n=3,4, `of_odd_primes`) + `fermatLastTheoremFor_of_five_le`.
- `Fermat/PrimeFive.lean` — the p ≥ 5 case PROVEN from `FreyPackage.false`,
  which is PROVEN from Mazur + B4 (see below).
- `Fermat/FLT/**` — 31 modules vendored from Buzzard's FLT project
  (github.com/ImperialCollegeLondon/FLT, Apache 2.0, imports rewritten
  `FLT.*` → `Fermat.FLT.*`; keep attribution headers when adding more).
  Reference clone for further vendoring: `~/cs/FLT` (read-only, never build
  there). Their architecture (Proof.lean "boss theorems" B1–B12) is the map;
  their sorries/`knownin1980s` become OUR sorries.
- mathlib pinned to the FLT project's exact rev `a3364faec429...`
  (lakefile.lean), toolchain `leanprover/lean4:v4.32.0-rc1`.

### Open sorry nodes (8) — the frontier

| Node | File | Notes |
|---|---|---|
| `FreyPackage.mazur` | `Fermat/FLT/FreyCurve/Mazur.lean` | Mazur's theorem + Serre §4.1; deep. |
| `FreyCurve.torsion_not_isIrreducible` (B4) | `Fermat/FLT/GaloisRepresentation/HardlyRamified/Frey.lean` | = Wiles + Ribet + no weight-2 level-2 cusp forms. Decompose via B5/B6 (hardly-ramified route, see FLT Proof.lean comments + 2026 EPSRC course PDFs in `~/cs/FLT/2026_EPSRC_TCC_course/`). |
| `FreyCurve.torsion_isHardlyRamified` | same file | Serre §4.1 + Tate curve theory. |
| `n_torsion_finite` | `Fermat/FLT/EllipticCurve/Torsion.lean` | needs division polynomials. |
| `n_torsion_card` | same | #E(k̄)[n] = n²; division polynomials; David Angdinata's PhD work covers this — but per policy it must be IN THIS TREE, so formalize it here. |
| `group_theory_lemma` | same | pure algebra, most tractable next node. Plan sketched below. |
| `Module.Finite (ZMod n)` instance | same | ⚠ FALSE as stated for n=0 (nTorsion 0 = whole group). Fix the statement (e.g. require 0 < n or [NeZero n]) as a marked VENDORING CHANGE, then prove. |
| `WeierstrassCurve.galoisRep` | same, line ~137 | ⚠ sorry-d DATA (a def!). Statements about it (Mazur, B4) are about an unspecified rep until this is constructed. High priority conceptually; needs the action's continuity. |

### Plan already worked out for `group_theory_lemma`

Hypothesis: `Nat.card (torsionBy ℤ A d) = d ^ r` for all `d ∣ n`, `0 < n`.
Goal: `torsionBy ℤ A n ≃+ (Fin r → ZMod n)`.
1. `Nat.card` positive ⇒ the n-torsion `T` is finite
   (`Nat.card_pos_iff`).
2. Structure theorem `AddCommGroup.equiv_directSum_zmod_of_finite`:
   `T ≃+ ⨁ i, ZMod (p i ^ e i)`; each `p i ^ e i ∣ n` (T is killed by n).
3. Torsion counting: `torsionBy` of a finite product ≅ product of
   `torsionBy`s (easy hand-rolled AddEquiv, componentwise);
   `Nat.card (torsionBy ℤ (ZMod m) d) = Nat.gcd d m`.
4. Count with d = q (each prime q ∣ n): forces #{i : p i = q} = r; with
   d = n and total card n^r: forces e_i = v_q(n) on those. So the multiset
   of factors is exactly r copies of q^{v_q(n)} for each q ∣ n.
5. Reassemble: `(⨁_{q ∣ n} ZMod q^{v_q(n)})^r ≃+ (ZMod n)^r` by CRT
   (`ZMod.chineseRemainder` / prime-factorization Pi equiv).
Suggested new file: `Fermat/FLT/EllipticCurve/TorsionCounting.lean` (own
work, not vendored — no FLT-project header).

## Workflow

- Build: `cd ~/cs/flt-worktree/fermat && lake build` (the `.lake` cache is
  already populated; a clean no-change build takes ~1 min).
- Axiom audit (run after every layer):
  write a scratch file `import Fermat` + `#print axioms fermat_last_theorem`
  (and the changed decls), run `lake env lean <file>`. Required result:
  subsets of `[propext, sorryAx, Classical.choice, Quot.sound]`.
- Commit in this worktree, push with `git push` (branch tracks
  `origin/flt-formalization`). Commit messages: end with the Claude
  co-author trailer as in `git log`.
- Update `PROGRESS.md` (tree + log) with every push.
- Sources for statements/proofs: (1) web search; (2) `~/cs/FLT` (their repo
  evolves — `git -C ~/cs/FLT pull` occasionally); (3) SOLO Oxford via
  claude-in-chrome browser automation (best-effort; captcha ⇒ abandon; see
  memory `solo-oxford-download-workflow`); (4) Anna's Archive MCP
  (`download_annas`; retry same md5 with different domain_index on TLS
  errors, never disable cert verification); (5) papers under
  `~/cs/dissertation/{papers,Books,Lecture Notes}` if materialized.
- **SOLO keepalive**: arm a session cron (e.g. every 6h at an off-minute):
  open solo.bodleian.ox.ac.uk in a NEW tab via claude-in-chrome, run one
  search, verify signed-in, close tab; if logged out/captcha, push-notify
  Deyao, never attempt login/captcha yourself. (The previous session's cron
  died with it.)
- Ping Deyao by push notification only for: blocked-on-user decisions,
  SOLO login expiry, or milestone completions. He reads pushes on his phone.

## Known hazards

- The old repo at `~/Documents/cs/dissertation` is iCloud-evicted and
  possibly unrecoverable locally; do NOT work there. Its uncommitted
  changes (CLAUDE.md edits, repo-memory files) may be lost — not your
  problem unless Deyao asks.
- Concurrent edits: other agents may edit files in OTHER worktrees; your
  branch is yours alone. If `git push` is rejected (non-fast-forward),
  `git pull --rebase` — never force-push.
- Lean gotcha: auto-generated instance names from the FLT project embed
  their module root (`..._fLT`); when vendoring a file that references one,
  name the instance explicitly (see `Deformations/Lemmas.lean`,
  `instAlgebraSubtypeMemValuationSubringVendored`).
