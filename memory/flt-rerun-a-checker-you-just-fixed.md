---
name: flt-rerun-a-checker-you-just-fixed
description: Merging a fix to a CHECKER invalidates every clean verdict the old one gave — re-run it on the tree you already certified
metadata:
  type: project
---

Release 31 (2026-07-31). `tools/merge/xdup.py` reported **0** qualified
cross-file duplicate pairs on `merger`. Nine merges later it reported **21** on a
tree whose Lean declarations were unchanged — because one of the nine branches
(`flt-lean-307`) carried a two-line fix to `xdup.py` itself. Both clusters were
hard `environment already contains …` import failures, i.e. release-blocking.

The old pair test was `a in cone[b]` — *does one module IMPORT the other?* Lean's
condition is weaker: **a collision happens as soon as SOME SINGLE module sees
both.** Two siblings under a common consumer collide and no import-cone pair test
can see it. (`HeckeAtkinLehner`/`HeckeQExpansion` under `Interface`;
`PrincipalDivisorDegree`/`CurveDivisorDegree` under `X0`.)

**Why:** a checker's diff is three lines and its blast radius is every previous
clean verdict. "Tooling change, no Lean impact, no need to re-verify" is exactly
backwards. The same reading makes a previous release's handover misleading —
release 30's truthfully said duplicates were clean, and the tree had two
release-blocking collisions in it.

**How to apply:** when a merge batch touches anything under `tools/merge/`, or
any script whose output you have quoted as evidence, re-run that script on the
tree *before* declaring the batch verified — and difference the result against
the last GREEN release, not against the previous merge base, since the defect
usually predates the base. See also [[flt-hidden-sorries-scans-main-repo]] and
[[flt-inventory-audits-understate-what-exists]]: all three are the same failure,
a measurement trusted past the validity of the instrument that produced it.
