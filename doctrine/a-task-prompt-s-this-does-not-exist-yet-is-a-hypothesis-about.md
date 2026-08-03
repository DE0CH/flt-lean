## A TASK PROMPT'S "THIS DOES NOT EXIST YET" IS A HYPOTHESIS ABOUT OUR OWN TREE
(2026-07-31.) A dispatch said `X0.lean` "can only speak of a bare `AddMonoidHom`
plus a separate `WeierstrassCurve.IsIsogeny` predicate" and set the task as *build
`End(E_ℚ̄)` as a ring*. It already existed — and both copies were findable in
seconds, by checks nobody was told to run:
* `Isogeny.lean`'s own **`## Main definitions` docstring** lists
  `WeierstrassCurve.endSubring` — "`End W` as a `Subring (AddMonoid.End W.Point)`,
  hence a `Ring`". The prompt named *that file* as the one lacking it.
* `grep -rn '^theorem End\.\|^def End\.' Fermat/` surfaced ~20 more in
  `IsogenyTrace.lean`, including `End.intCast_injective` and
  `End.torsionRep : End V →+* Module.End (ZMod n) (V.nTorsion n)` — which was
  item 3 of the three-item task, already proven.
The prompt did say to check `~/cs/FLT` and mathlib for prior art. **Both are
EXTERNAL.** That is the gap: absence claims get audited against other people's
repositories and never against ours, and the file cited as deficient is very often
the file that contains the thing.
So, before writing any new infrastructure: (1) read the `## Main definitions`
block of every file the prompt names; (2) `grep -rn '^theorem <Namespace>\.'
Fermat/` for the namespace you are about to create; (3) only then look outward.
**And a near-duplicate is worse than a duplicate.** The first draft here named a
lemma `End.intCast_injective`, colliding exactly with `IsogenyTrace.lean`'s. A
same-name collision across two modules is invisible until some third module
imports both — the cross-file half of the duplicate-declaration hazard in the
interface-split section above, which a per-file scan cannot see.
