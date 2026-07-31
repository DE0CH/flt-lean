---
name: flt-port-may-exist-in-unimported-sibling
description: A "port this ℚ theorem to a general field" leaf may already be PROVEN in a sibling module your file does not import — reachable from the root, so green and counted, but invisible from the consumer that needs it
metadata:
  type: project
---

`exists_ellipticScheme_weierstrassChart_addEquiv_field` (`EllipticScheme.lean`) was
priced — by its own docstring, by the task prompt, and by my first inventory — as a
~6500-line `ℚ → arbitrary field` port of 106 declarations. Two of its four inputs
were **already proven over an arbitrary field**, sorry-free, in
`Fermat/FLT/Mathlib/AlgebraicGeometry/EllipticCurve/ProjectiveModelOverField.lean`
(103 declarations, namespace `WeierstrassCurve.Projective.OverField`), together with
`exists_projChartRingEquiv`, `projChart_jacobian_span_eq_top`, `dehomogenizeAt`,
`homogenizeAt` and `projInfty_comp_projToSpec`. A one-line `public import` closed two
leaves and shrank a third. A parallel `OverField` development also sits in
`Modularity/MoretBailly.lean` (`ProjGroupLawOverField`, `isProper_projToSpecOverField`).

**Why every instrument missed it, and this is the new part.** CLAUDE.md's "fourth
invisibility class" is a module unreachable from `Fermat.lean` — never compiled, so
invisible to the build, the warning set and the census. This was the *opposite* case
and is not covered there: `ProjectiveModelOverField.lean` **is** reachable from the
root (via `MoretBailly.lean`), so it compiles, is green, and is counted. It was
invisible only **from the file that needed it**, because `EllipticScheme.lean` did
not import it. A module can be perfectly healthy in the global build and still be
unreachable from the one proof that wants it.

So `lake build <YourModule>` is *evidence of absence for your import cone only*. It
says nothing about the rest of `Fermat/`, and neither does reading your own file.

**Why:** absence audits here habitually ask two questions — "is it in mathlib?" and
"is it proven over `ℚ` in THIS file?" — and a port leaf is exactly the shape where
the answer to both is "no" while the theorem exists three directories away under a
name built from `OverField`/`_field`/`OverRing` rather than from the consumer's
vocabulary. Cf. [[flt-missing-machinery-may-be-downstream]],
[[flt-absence-audit-names-one-module]], [[flt-grep-project-not-just-mathlib]],
[[flt-inventory-audits-understate-what-exists]] — this is the same failure with a new
mechanism, and it recurred despite all four being on file.

**How to apply:** before cutting or accepting ANY "generalise/port this proven
theorem" leaf, grep the whole tree for the CONCLUSION's shape, not the name:

    grep -rn "SmoothOfRelativeDimension 1 (projToSpec" Fermat/ --include=*.lean
    grep -rln "OverField\|_field\b\|OverRing" Fermat/ --include=*.lean

Then check whether your file imports the hit — `grep -n "<module>" <yourfile>` — and
if not, whether importing it would cycle (read its own import list; a
`Fermat/FLT/Mathlib/...` leaf module usually imports only mathlib and one sibling).
Adding the import is nearly always cheaper than the port, and it also removes a
duplicate maintenance surface. Watch for two traps when delegating: the ported twin
may take the base field EXPLICITLY where the `ℚ` version leaves it implicit, and
opening its namespace unrestricted can pull in scoped notation that collides —
`open _root_.WeierstrassCurve.Projective` made `(E⁄F).Point` an `Ambiguous term`
against `WeierstrassCurve.Affine`'s `⁄`, fixed by opening a name list instead.
