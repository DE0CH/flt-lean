---
name: flt-repair-tasks-die-at-a-publish
description: "A repair task is invalidated atomically by a PUBLISHED release, and the queue audit's leaf-name filter can never garbage-collect it"
metadata: 
  node_type: memory
  type: project
  originSessionId: eefa6fc2-c1d5-4f74-8266-ae44d75166ab
  modified: 2026-08-02T06:27:24.641Z
---

A queue task that names WOUNDS (a dropped `open`/`section`/`variable`, a stale
rename, a declaration used above where it is declared, a missing
`maxHeartbeats`) is not like a leaf task. Repairing those wounds is *what
publishing a release consists of* — release 33's handover: "Eight consecutive
repair rounds across the dark cone, and not one was mathematics."

So a repair task does not decay gradually the way a leaf task does. **It dies
all at once the instant the release publishes**, together with every other
repair task queued during the hold. Release 33 was the first publish in six
releases, so every repair task from those five holds went obsolete
simultaneously.

**The audit structurally cannot delete them.** Its keep-test is "does this task
name a leaf that is still open?" A repair task names no leaf, so it survives iff
its prose happens to quote some still-open leaf name. Measured 2026-08-01:
`queue1`'s round-6 X0 repair task ("X0 is RED with 33 errors") survived release
33's audit because it quotes
`exists_ringHom_gamma0GITPresentationOver_of_atlas_charDvd`, still a leaf — while
all six wounds it describes were repaired and X0 elaborates `EXIT=0`, 0 errors,
101 `sorry`s. It is immortal and will keep drawing agents.

**Why:** This is the mirror of [[flt-frozen-main-rots-the-queue]]. A HELD release
rots leaf tasks (the fleet keeps proving); a PUBLISHED release rots repair tasks
(the merge worker keeps fixing). Each is invisible to the check written for the
other.

**CONFIRMED 2026-08-02, and the prediction in the paragraph above fired exactly
as written.** `flt-lean-74` was dispatched at that immortal X0 repair task — by
then re-stamped "39 remaining errors as of release 30", with the wounds
classified into nine declaration-order breaks and twelve genuine errors. All of
it was gone. Measured on the current tree: `lake build Fermat.FLT.ModularCurve.X0`
→ `Build completed successfully (5276 jobs)`, `EXIT=0`, **0 errors**; whole tree
→ 5702/5703 targets, `SORRY GATE FAILED` the only error, 377 sorries. So the cost
of this class is now known: **one full agent dispatch per stale repair task per
release**, and this one has survived at least two audits.

**How to apply:**
- Receiving a repair task: `cat ~/.flt-release-lake/sha` and
  `ls tools/merge/RELEASE-*-HANDOVER.md | tail -1` — did it PUBLISH? If your
  module is in the published green cone, every wound-shaped item is gone. Check
  one, confirm, decline. Do not check six.
- **Reproducing costs two commands when the snapshot sha equals your HEAD**,
  which is the normal state right after a publish — i.e. exactly when a stale
  repair prompt is most likely. `git merge --ff-only merger`, then
  `rsync -a --delete ~/.flt-release-lake/build/ /scratch/chend-flt/flt-lean-N/.lake/build/`
  (~2 min) makes the confirming build a pure replay.
- Judge the whole-tree build by the NEGATIVE test — `EXIT=1` with
  `SORRY GATE FAILED` as the only error, zero other `error` lines, and a job
  high-water mark within one of the target count. A build that died early also
  has no errors in the modules it never reached.
- Having declined: do not stop. You hold a fully warm green tree, which is the
  most expensive prerequisite for any leaf in that module — spend the cycle
  there. `flt-lean-74` closed one X0 leaf and re-cut another in the same run.
- Checking a "used above where declared" symptom: strip comments first. In this
  tree most occurrences of a name are backticked docstring prose, and a naive
  `grep -n` reproduces order violations that do not exist.
- Writing one: stamp the release number and whether it was held, in line 1.
- Merge worker: after a publish, sweep the queue by hand for tasks naming a FILE
  and an ERROR COUNT rather than a declaration. Re-verify coverage afterwards —
  it is a queue deletion.

See also [[flt-release-deletes-nonleaf-tasks]], [[flt-queue-coverage-is-one-sided]].
