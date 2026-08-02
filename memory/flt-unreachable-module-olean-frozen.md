---
name: flt-unreachable-module-olean-frozen
description: "A module outside Fermat.lean's import closure is never rebuilt, so its olean is frozen at the last release it was reachable — and a co-import probe loading it returns a false \"no collision\""
metadata: 
  node_type: memory
  type: project
  originSessionId: 4fbf9aba-acfd-41aa-94b5-e6329c2d91d5
  modified: 2026-08-01T11:18:14.467Z
---

`lake build` builds the ROOT's import closure. A module outside it is never
built again, so its `.olean` is frozen at the last release in which it *was*
reachable — permanently, not until the next build.

2026-08-01, `flt-lean-263`: release 31 dropped `X0.lean`'s import of
`Mathlib/AlgebraicGeometry/CurveDivisorDegree.lean` over a duplicate-declaration
collision with `PrincipalDivisorDegree.lean`, making it the tree's one
unreachable module. A two-line scratch importing BOTH then returned `EXIT=0`
with no output — *"no collision"* — because it loaded the frozen olean, which
predates the duplicates. The collision is real and plainly visible in the
sources.

**When a probe disagrees with what the source plainly says, the probe is testing
a different tree.** Before believing any `lake env lean` result involving a
module you are not actively building, check whether it is in the root closure
(BFS the `^(public )?import Fermat…` edges from `Fermat`, asserting each visited
file exists); if it is not, `lake build` that module first.

Two riders from the same run:

* the collision was **two lemmas** (`Scheme.ord_one`, `Scheme.ord_inv`,
  character-for-character identical, `@[simp]` on both sides). A 16-line import
  comment recorded the collision and never its SIZE. Measure the QUALIFIED
  declaration-name intersection before accepting a "deliberately not imported"
  note — and do not confuse it with a LAST-COMPONENT match, of which this tree
  has thousands.
* restoring the edge puts the orphan back in the closure, so its `sorry`s become
  countable and the reported frontier RISES. That is disclosure; say so, or it
  reads as a regression. It also closed the `frontier.py` 380-vs-377 discrepancy
  release 33 recorded, and left every module under `Fermat/` reachable.
* **the closure scan invents orphans if its import regex is anchored at `$`.**
  This tree annotates imports (`public import Fermat.X -- reason`), so
  `^\s*(?:public\s+)?import\s+(Fermat[\w.]*)\s*$` silently drops those edges; my
  first scan reported a phantom second orphan that way. Strip `--` first, and
  do not anchor at end of line.

See [[flt-frontier-tools-hardcode-staging-root]] for the neighbouring trap of
trusting a scan without checking what tree it is reading.
