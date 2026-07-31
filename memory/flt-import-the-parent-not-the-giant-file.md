---
name: flt-import-the-parent-not-the-giant-file
description: To iterate on a leaf inside an 80k-line module, import that module's PARENT and re-declare by hand the handful of downstream names your proof mentions — 90 seconds instead of 40 minutes
metadata:
  type: project
---

The standing scratch-module rule says "import only what you need". The sharper
form, when the TARGET's own file is the expensive one:

**Import the target file's PARENT, and inline copies of the few declarations from
the target file that your proof actually names.**

Measured 2026-07-31 on `Fermat/FLT/ModularCurve/X0.lean` (81 530 lines):

* `lake build Fermat.FLT.ModularCurve.X0` — **~40 minutes**, single-threaded, and
  it is what a scratch module that `import`s X0 has to wait for first;
* a scratch importing `Fermat.FLT.ModularCurve.RelativePicard` (X0's parent, whose
  `.olean` the release snapshot already carries) plus two hand-copied declarations
  — `IsSmoothProperCurve` (a 3-field structure) and `AbelianSchemeStruct.listSum`
  (a 2-line recursion) — **90 seconds**, and it verified a 130-line tensor-calculus
  development on the first try.

The whole development then transplants into X0 unchanged; only the two inlined
copies are deleted. It works because a leaf's proof usually mentions very little
of its own enormous file — here 2 declarations out of thousands — while every
lemma it really leans on lives upstream.

Two cautions. (1) Match the header treatment: `module` + `public import` +
`@[expose] public section`, or the import is not expressible. (2) The inlined
copies must be `def`/`structure` clones, so dot-notation like `hf.isProper` and
recursion equation lemmas behave identically; if you find yourself needing a THIRD
or FOURTH copy, the parent is the wrong cut point.

Related: [[flt-ssh-build-needs-cd-and-elan-path]] (the build itself needs
`PATH="$HOME/.elan/bin:$PATH"`; a detached `setsid nohup` build survives a session
teardown that kills every `run_in_background` waiter, so launch the build detached
and the waiter separately).
