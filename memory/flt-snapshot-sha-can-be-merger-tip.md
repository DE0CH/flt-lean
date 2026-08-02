---
name: flt-snapshot-sha-can-be-merger-tip
description: "After a release publishes, ~/.flt-release-lake/sha equals merger's tip — so a merger-based branch seeds for free and a prompt's \"3h build\" estimate is wrong"
metadata: 
  node_type: memory
  type: project
  originSessionId: 692cb29f-c796-4c03-8a9c-fa5496be3b13
  modified: 2026-08-01T16:13:25.700Z
---

The seeding doctrine assumes `~/.flt-release-lake/sha` tracks `main` and that
`merger` runs ahead of it, so a merger-based branch has no artifacts. **In the
window after a release publishes this inverts: the snapshot sha IS `merger`'s
tip.** Measured 2026-08-01 (`flt-lean-139`, release 33): the task prompt priced
`lake build Fermat.FLT.FreyCurve.MazurTorsion` at "~3h from cold"; after
`git merge merger` the snapshot sha equalled HEAD exactly, so a 15-second
`rsync -a --delete ~/.flt-release-lake/build/ .../.lake/build/` made the
pre-edit build a sub-30-second replay and left only the edited file to
elaborate.

**Why:** a prompt's build estimate describes the tree its writer had. A release
landing in between invalidates it in the direction that makes agents skip the
real in-file verification and ship scratch-only evidence.

**How to apply:** before pricing anything, run `cat ~/.flt-release-lake/sha`
then `git diff --stat <that sha> HEAD -- Fermat/`. Empty means the snapshot is
your tree whatever branch you stand on — seed it and build freely. It also
removes both objections to [[flt-target-exists-only-on-merger]] (unknown build
state, missing artifacts), so base on `merger` without hesitation and say in
`to_merger` that the snapshot certified it. Take the pre-edit replay build as a
baseline log: comparing `declaration uses 'sorry'` sets before and after, by
attributing each warning line to its enclosing declaration, turns a "`1 → 1`
recut" claim into a receipt.
