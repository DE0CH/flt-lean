---
name: flt-import-scan-must-not-anchor-eol
description: An import-reachability regex anchored at end-of-line drops `import Fermat.X -- comment` and manufactures a phantom unreachable module
metadata:
  type: reference
---

`r'^(?:public\s+)?import\s+(Fermat[\w.]*)\s*$'` is wrong. Import lines in this tree
carry trailing comments — `public import Fermat.FLT.Mathlib.RingTheory.Localization.BaseChange
-- removing this breaks a simp proof` in `Fermat/FLT/DedekindDomain/IntegralClosure.lean`
is a real one — so the `$` drops the edge and the imported module looks orphaned.

**Why:** at release 32 this made a BFS report two modules unreachable from
`Fermat.lean` when the true answer is one (`CurveDivisorDegree.lean`; 401 of 402
modules are in the closure). The wrong number was written into the release handover
before the check was re-run.

**How to apply:** drop the `$`, and skip lines whose first token is `--` or `/-`.
Also assert that every visited module's file EXISTS — a swallowed `FileNotFoundError`
truncates the walk and manufactures exactly the "unreachable" answer you were testing
for. Same family as [[lean-identifier-regex-swallows-brackets]] and
[[flt-rerun-a-checker-you-just-fixed]]: a scan that under-reports does not miss, it
CERTIFIES.
