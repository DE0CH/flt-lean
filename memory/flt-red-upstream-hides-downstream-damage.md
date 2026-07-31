---
name: flt-red-upstream-hides-downstream-damage
description: "Every module except X builds" is a claim about the modules lake REACHED; behind a red module, merge damage accumulates unreported for as many releases as it stays dark
metadata:
  type: project
---

`lake build` stops at the first red module in a cone, so everything downstream is
UNSEEN rather than fine. `ModularCurve/X0.lean` was red from release 25 to 31; when
it went green at release 32 the very next module, `X1.lean`, had three errors of its
own that no build, no `declaration uses 'sorry'` warning set and no frontier scan had
been able to report.

**Why:** every release handover in that window truthfully said "every module except
X0 builds", and every one of them was a statement about reachability, not soundness.

**How to apply:** budget downstream repair in proportion to how long the blocker was
dark, and do not read a green-so-far build log as a verdict — wait for the `EXIT=`
line you appended yourself. To see into a darkened module before its cone is fixed,
elaborate it directly with `lake env lean` against the previous release's oleans
(`~/.flt-release-lake/build` via a `cp -rs` farm on `LEAN_PATH`). Related:
[[flt-complementary-structure-fields-split]].
