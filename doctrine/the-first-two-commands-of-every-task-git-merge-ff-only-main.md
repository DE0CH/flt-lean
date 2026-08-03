## THE FIRST TWO COMMANDS OF EVERY TASK: `git merge --ff-only main`, then `git show merger:<file>`

(2026-07-31, `flt-lean-232`, both measured on the fleet rather than inferred.) A prover agent
under the Python loop can be handed a worktree that is hundreds of commits stale AND a target
that was proven a day earlier. Both are cheap to detect and neither is detectable from inside
the task prompt.

**1. YOUR WORKTREE MAY NOT BE AT `main`, AND THE LOOP WILL NOT SAY SO.** `flt-lean-232` was
dispatched at `9a2ca10d` with `main` at `d451d20b` — **704 commits behind**. A sweep of the 112
live jobs at that moment found **23 behind `main`, 6 of them by the full 704**; the other 17 were
2 behind, which is only the tooling commits after the rebaseline sha and harmless. So this is not
a one-off: it is roughly 5% of dispatches, silently.

**THE CAUSE IS THAT NOTHING ADVANCES A WORKTREE — NOT THE LOOP, NOT THE RELEASE, NOBODY.** This
is worth stating plainly because the old orchestrator DID repoint at dispatch, the sections above
still describe that hook, and it is gone. Read the production code: `flt-loop.py`'s `do_spawn`
composes a prompt and runs `cd <worktree> … claude`, and that is the whole of it — no `merge`, no
`checkout`, no `branch -f`. The merge worker works in `~/flt-staging`; its five ordered duties are
merge, build the snapshot, rewrite `queue1`, stamp `AUDITED:`, stamp the snapshot sha. **None of
them touches a pool worktree.** So a worktree sits at whatever `main` was when its last occupant
last merged, indefinitely.

Which is exactly why the current ones are current: **the agents advance them.** The merge worker's
queued task text opens with *"Run `git merge main`, then `lake build …`"*, so every agent on a
merger-written task drags its worktree forward as a side effect. Tasks that lack that line — older
`queue1` entries, and the one that produced this section — leave the worktree wherever it was. The
repair belongs in the queue text, and it is one line: **put `git merge --ff-only main` in every
task's preamble.**

**Do not "fix" this in `flt-loop-fs.py`.** That file is the SIMULATOR — its `repo()` is
`~/.flt-loop/repo`, a stand-in repository for testing `flt_loop_rows.py`, not `~/flt-lean` — and
its `grepo("branch", "-f", j["worktree"], "main")` is simulation, not the dispatcher. It would not
work against the real pool anyway; git refuses to force a branch that a linked worktree has
checked out, which is every worktree in the pool:

    $ cd ~/flt-lean && git branch -f flt-lean-232 <sha>
    fatal: cannot force update the branch 'flt-lean-232' used by worktree at '/home/chend/flt-lean-232'
    EXIT=128

Any loop-side repoint has to run INSIDE the worktree (`git -C <wt> merge --ff-only main`), and
`--ff-only` rather than a forced checkout, so that a worktree still holding someone's uncommitted
work fails loudly instead of losing it.

**The free detector is the line number in your own prompt.** The task said
`Fermat/FLT/ModularCurve/X1.lean:15893`; the file had **10391 lines**. A `Read` at that offset
returns "the file is shorter than the provided offset", and a `grep` for the target returns
NOTHING — which reads exactly like "this leaf does not exist / was renamed" and is the wrong
conclusion. Before believing any such absence:

    git merge-base --is-ancestor HEAD main && git rev-list --count HEAD..main   # 0 = current
    git merge --ff-only main                                                    # if behind

It is safe: the worktree is clean at dispatch and its branch is an ancestor of `main`, so this is
a fast-forward, never a merge. Do it FIRST, before reading anything.

**2. THEN CHECK `merger`, BECAUSE THE LOOP'S QUEUE AUDIT STRUCTURALLY CANNOT.** `queue1` records
its audit as `AUDITED: <main sha>`, and `flt-loop-fs.py`'s release-time audit computes
`open_leaves()` from the repo at `main`. That is correct by its own contract and it means the loop
**cannot see a leaf proven on `merger` and not yet released** — every such leaf is re-dispatched,
guaranteed, once per release window. This is the fifth invisibility class above, but under the
Python loop it is no longer a judgement call that a careful orchestrator might catch: it is
mechanical, and the only thing standing in front of it is the agent.

`exists_nonconstant_toAbelianScheme_of_notGeometricallyRational` was `sorry` on `main` and
**PROVEN on `merger`** (via `flt-lean-34`, merger commit `df076668`), by decomposition into two
new residues. One command would have found it, and it is the same command CLAUDE.md already
prescribes:

    git show merger:Fermat/FLT/ModularCurve/X1.lean | grep -n <your target>

**3. IF YOUR TARGET IS ALREADY DONE, DO NOT GO LEAF-SHOPPING ON `main` — THE FLEET IS SATURATED.**
Measured the same day: `flt-frontier.py` gave **320 direct leaves** and 112 live jobs named all but
**3** of them in a `TARGET:` line. All three turned out to be accounted for anyway — two were
already `queue2` targets, and the third
(`exists_globalFrobCharScalar_atPrime_of_coherentLevelScalar_finiteBase`) was **already proven on
the unmerged branch `flt-lean-101`** and re-cut there into a queued successor. **Unowned work on
`main` was empty**, and taking an owned leaf duplicates a live agent.

Note what the third one shows: a leaf can be simultaneously open on `main`, absent from every
live `TARGET:` line, and finished — and the evidence lived in the BODY of an unrelated queue
entry, not in any ownership record. So grep `queue1`/`queue2` in FULL, not just their `TARGET:`
lines, before concluding anything is free.

The work that IS unowned is the **residues cut on `merger` since the last release** — new leaves
nobody can be dispatched at, because they do not exist on `main`. Those belong in your `queue`,
written as full task prompts. That is the highest-value output an agent with a finished target
has, and it is invisible to everyone else by construction.

**Do NOT re-prove the target on `main` "so the branch carries it".** `merger` already has it; a
second proof of the same theorem is a name collision the merge worker must resolve by discarding
one, which is a choice that belongs to an author, not a merge.

