---
name: flt-read-the-module-docstring-first
description: A task prompt's "this object does not exist yet" is an absence claim about OUR tree; check the named file's own Main-definitions docstring and grep `^theorem <Namespace>\.` before building it
metadata:
  type: feedback
---

A dispatch prompt said `X0.lean` "can only speak of a bare `AddMonoidHom` plus a
separate `WeierstrassCurve.IsIsogeny` predicate", and set the task as *build
`End(E_Qbar)` as a ring*. It already existed, in two places, and both were
findable in seconds:

- `Isogeny.lean`'s own **module docstring** lists `WeierstrassCurve.endSubring`
  under `## Main definitions` — "`End W` as a `Subring (AddMonoid.End W.Point)`,
  hence a `Ring`". The prompt named that very file as the place the API was
  missing from.
- `grep -rn '^theorem End\.\|^def End\.\|^noncomputable def End\.' Fermat/`
  surfaced ~20 more in `IsogenyTrace.lean`, including `End.intCast_injective`
  and `End.torsionRep : End V →+* Module.End (ZMod n) (V.nTorsion n)` — which
  was item 3 of the task, already proven.

**Why:** the prompt told me to check `~/cs/FLT` and mathlib for prior art. Both
are *external*. Nothing told me to check our own tree, and the file it pointed at
as deficient was the file that contained the thing. An absence claim in a prompt
is a hypothesis about a moving tree, written by someone who did not grep — the
same class as [[flt-inventory-audits-understate-what-exists]] and
[[flt-missing-machinery-may-be-downstream]], but cheaper to refute than either.

**How to apply:** before writing any new infrastructure, in this order —
(1) read the `## Main definitions` docstring of every file the prompt names;
(2) `grep -rn '^theorem <Namespace>\.' Fermat/` for the namespace you are about
to create; (3) only then look outward. Had I done this the task would have
started as "add the imaginary quadratic ORDER on top of the existing ring",
which is what it actually was, instead of re-deriving a torsion-count argument
that `End.intCast_injective` already owned.

Corollary that also bit: a near-duplicate is worse than a duplicate. My first
draft named its lemma `End.intCast_injective`, colliding exactly with
IsogenyTrace's. Nothing catches that until some third module imports both — see
the interface-split / duplicate-declaration hazard in `CLAUDE.md`.
