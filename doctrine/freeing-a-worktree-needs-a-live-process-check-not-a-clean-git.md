## Freeing a worktree needs a LIVE-PROCESS check, not a clean `git status`

(2026-07-27, orchestrator error.) `flt-lean-86` was marked `ready` and dispatched into **while another
agent was still working in it**. Two agents then shared one worktree: the newcomer found *two* `lean`
processes elaborating `WeilPairing.lean` into the same `.olean`, its `git add -A` swept the other agent's
uncommitted `HasseBound.lean` edits into an unrelated commit, and when it restored the file the other
agent **rewrote it again** — which is how the collision was finally diagnosed. It also made
`MazurTorsion` look red (two errors) from a defect that was neither on `main` nor in either agent's work.

The trigger was a *correct* observation read as the wrong conclusion. A completing agent reported that
`flt-lean-86` "sits at `81eb57e2`, clean, and its branch was fast-forwarded — nobody is working on it."
Every clause was true at the instant it was measured. **A worktree between edits is indistinguishable
from an idle one by `git status` alone**, and an agent doing a 25-minute `lake build` touches nothing for
25 minutes.

So the rule is: **before promoting any worktree out of `claimed`, check the OWNING HOST for live
processes**, not just the tree:

    H=$(cat ~/.flt-worker-host/flt-lean-N)
    ssh $H "pgrep -af '[l]ean.*flt-lean-N'"

and cross-check `python3 flt-owner.py --all` (latest dispatch per worktree, from the transcripts) against
the completion notifications actually received. **The notification stream is the ground truth for "this
agent has stopped"** — a third party's report that a slot looks idle is not. This is the same principle
`.claude/skills/fleet-revive/SKILL.md` states for staleness sweeps ("staleness cannot distinguish working
from dead"), applied to the promotion direction.

Corollary, and the reason this was recoverable: the intruding agent **tagged the other agent's WIP**
(`flt-lean-86-hassebound-wip`) before touching anything, and left the working tree dirty by design. When
a collision is discovered, preserve first and report loudly; do not clean up to make `git status` tidy.

