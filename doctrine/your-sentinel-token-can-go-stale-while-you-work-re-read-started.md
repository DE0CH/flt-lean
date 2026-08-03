## YOUR SENTINEL TOKEN CAN GO STALE WHILE YOU WORK — RE-READ `.started` BEFORE WRITING IT

(2026-07-31, `flt-lean-15`. Cost nothing only because it was noticed; the failure mode is
total, silent, and looks exactly like dying.)

The token in your task prompt is the token that was current **when you were spawned**. The
loop ROTATES it whenever it resumes a job. So an agent that is resumed mid-run — which is
routine, and is what a bare `continue` usually is — holds a prompt naming a token the loop
no longer accepts. Concretely, on this run:

    prompt said        115c51de
    .started said      6c69a75c   (rewritten 5 minutes AFTER the sentinel was written)
    .json said         6c69a75c   with "resume": true and this session's own id

A sentinel written under the old token is **ignored in full** — `queue`, `to_merger` and
all. The loop then sees no sentinel, concludes the agent died, and starts a replacement on
the same worktree. Everything the run learned is discarded, and the branch is left for a
successor who will re-derive it. Note the shape: the work was committed and green, the
report was written and accurate, and it would still have evaporated.

**So the sentinel write is a two-step, always:**

    cat ~/.flt-loop/jobs/<worktree>.started      # the token the loop expects RIGHT NOW
    # write the sentinel using THAT, not the one in your prompt

`.started` is authoritative; `.json`'s `token` field agrees with it and is a fine
cross-check. If they disagree with your prompt, your prompt is the stale one — you were
resumed. Rewriting an already-written sentinel with the fresh token is correct and safe:
the content is unchanged, only the freshness handshake moves.

Corollary, and it is the general form of this and of the `flt-loop spawn/liveness race`
note: **any identifier the loop handed you at spawn is a snapshot, not a fact.** Re-read it
from disk at the moment you need it. The loop's whole state is on disk precisely so that
this is possible; reasoning from what your prompt said is reasoning from a cached value.

Second corollary, for whoever is checking whether work got lost: `~/.flt-worktree-pool`
reading `batched` does NOT mean your sentinel was accepted. Those are independent pieces of
state, and this run observed `batched` while its sentinel was being ignored.

