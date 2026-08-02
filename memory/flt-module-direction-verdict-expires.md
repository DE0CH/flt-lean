---
name: flt-module-direction-verdict-expires
description: A leaf's "blocked by module direction" verdict expires when the hoist lands; re-grep the blocking module's own import block before believing it.
metadata:
  type: project
---

A leaf whose docstring says the theory it needs is unreachable because that theory's
module IMPORTS the leaf's file is recording a fact with an expiry date, and nothing
writes the date down. On 2026-08-02 `exists_frickeSlash_eq_smul_of_isNewEigenformAt`
(`ModularCurve/X0.lean`) still carried such a verdict in bold; the hoist it asked for
had landed as `Modularity/HeckeAtkinLehner.lean`, whose only project imports are
`HeckeOperator` (no project imports) and `HeckeQExpansion` (imports only
`HeckeOperator`) — neither reaches `X0.lean`. The leaf had been provable for a release.

**Why:** the docstring's own refuting check was phrased as an ABSENCE ("find an import
path back into X0"), which is expensive to establish and easy to believe. The cheap
positive form is to read the blocker's import block:
`grep -n '^public import Fermat\|^import Fermat' <module holding the theory>`, then
`python3 tools/merge/cyclecheck.py`. Seconds, no build.

**How to apply:** before accepting any module-direction blockage, grep the blocking
module's imports. Land the result in a NEW module between the two — grep where the
vocabulary is actually DECLARED first (here all but one name was upstream of X0 in
`WeightTwoEigenform.lean`), so the giant file needs one import line and a short
assembly. Do NOT re-namespace a verified block: `Fermat.Gamma0GL` and
`Modularity.Gamma0GL` are defeq but not syntactic, so `rw` leaves goals printing `X = X`.

See [[flt-handoff-block-pays-off]] for the banked-block half of this.
