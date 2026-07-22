> NOTE (2026-07-22, post-split): this repo is the standalone flt-lean
> extraction; paths below have been adjusted (project root = former
> fermat/ folder).

# Session handoff — 2026-07-22

Written at Deyao's request: the driving session is being moved to a new
environment. This file is the transient state snapshot; the durable
mission/policies live in `CLAUDE.md` (repo root), the tree state in
`PROGRESS.md` + `progress-entries.json`.

## FIRST ACTIONS FOR THE SUCCESSOR (in order)

1. **Update the session guard**: write your own session id into
   `.claude/stop-hook-session-id` (repo root), else the Stop hook will
   refuse to drive you. Launch from the REPO ROOT
   (`/Users/deyaochen/cs/flt-lean`).
2. **Verify the prune commit `ae59df2`**: the head commit contains the
   PROVEN `hres` closure (verified clean before the prune) PLUS an
   unused-have prune that has NOT been re-verified. Run
   `mcp__lean-lsp__lean_diagnostic_messages` on
   `Fermat/FLT/EllipticCurve/WeilPairing.lean` (severity error)
   and WAIT — full elaboration of the μ-theorem takes ~40 minutes wall
   (two machine-generated mega `linear_combination`s under
   `maxHeartbeats 16000000` at line ~3011). "still_elaborating" for
   30-50 min is NORMAL, not a hang. If the prune broke a name, the fix
   will be obvious (unknown identifier); if clean, proceed.
3. After verification: `lake build Fermat.FLT.EllipticCurve.WeilPairing`
   (refreshes the daemon state; expect it to be SLOW for this module),
   then continue the loop.

## WHERE THE MATHEMATICS STANDS

Active node: `WeilPairing.exists_weilPairing_mu`
(`Fermat/FLT/EllipticCurve/WeilPairing.lean`, ~10k lines).
12 sorried declarations remain in the whole tree; this node is the wip
frontier (flag set in `progress-entries.json`).

**JUST COMPLETED (this session's arc): the entire `hstepR` reciprocity
chain is PROVEN** — inside `hrecgen`'s proof, `hstepR`'s
`hstarinst`/`hgrand`/`hstitch`/`hscalar`/`hword0`/`hword1`/`hword2`
all closed. Key design decisions (full detail in `HWORD2-NOTES.md` and
the progress entry):
- Amendment (α): `xQR ∉ F'` in the `IsWeilValue` predicate.
- The (γ) M-design: the zero-sum element `t` factors through two chords
  meeting at `M = Q⊕R₁⊕R₃` with `xM ∉ F'` (hrecgen binders
  `xM yM hM hMc hxMF'`, plus the UNUSED-SO-FAR mirror binder group
  `xM' …` for `P⊕S₁⊕S₃`, both discharged in `hcross`).
- The final telescope was assembled MECHANICALLY: the bookkeeping
  engine lives at the scratchpad (`telescope.py`,
  `hword2-final2.json`, `telescope-out.json` under
  `/private/tmp/claude-501/-Users-deyaochen-cs-flt-worktree/4f31fd20-*/scratchpad/`
  — NOTE: scratchpad is session-specific and may be GONE in the new
  environment; the METHOD is what matters and is described in
  `HWORD2-NOTES.md`: dump goal via lean_goal, extract raw hypothesis
  sides, α-normalize lambdas scope-correctly, factor-multiset
  substitution chains, emit contexts as linear_combination
  coefficients).

## REMAINING SORRIES INSIDE THE μ-NODE

1. **`hstepS`** — the S-side telescoping step, mirror of `hstepR`
   (statement already in place, proof = sorry). Strategy: replay the
   ENTIRE hstepR construction with the roles of (S₁,PS₁) and (R₁,QR₁)
   swapped: zero-sum element with divisor over PS₁/⊖S₁/S₃/⊖PS₃-type
   points, chords meeting at M' = P⊕S₁⊕S₃ (binders ALREADY in hrecgen,
   already discharged in hcross), same hgenfac word for aQ-side, same
   telescope. Expect heavy but mechanical replay; reuse the engine.
2. **`hleg1`–`hleg6`** — bilinearity (2), alternation, nondegeneracy,
   p-th-powers-are-1, Frobenius naturality of the pairing value.
3. Elsewhere in the tree: `torsion_flat_of_good_reduction`,
   `exists_frobenius_conj_mem_coset`,
   `torsion_flat_of_multiplicative_reduction`, `mazur_classification`,
   and the rest listed by the Stop hook / PROGRESS.md.

## INFRASTRUCTURE NOTES

- **Hooks**: Stop hook = `.claude/check-sorries.py` (drives the loop,
  queries the persistent daemon `lean-daemon.py`); NEW PreToolUse
  hook = `.claude/lean-pretool-reminder.py` (fires before every
  lean-lsp call: sorry only in place of a proof, every have consumed —
  Deyao's no-floating rule at the have level; the just-committed prune
  enforced it retroactively).
- **Elaboration cost**: the μ-theorem is now VERY heavy (~40 min).
  Consider (only if it becomes blocking, ask Deyao): splitting hstepR
  into standalone private lemmas, or extracting the mega-lc's.
  The `unusedSimpArgs` linter fires on some simp lists — warnings only.
- **Commit discipline**: plain `git commit` (ssh-signing via
  Bitwarden agent — if "No private key found", the agent is
  locked/down; ask Deyao). Trailers: Co-Authored-By + Claude-Session.
  Never push --force. Update progress-entries.json + run
  `python3 progress-tree.py`, never hand-edit PROGRESS.md.
- **Loop policy**: never end a turn while sorries remain and work is
  continuable; report the sorried-declaration count (currently 12) in
  every user-visible message; wip flags current at block boundaries;
  PushNotification when the μ-node is proven or abandoned.
