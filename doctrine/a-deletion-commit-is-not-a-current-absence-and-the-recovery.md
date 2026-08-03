## A DELETION COMMIT IS NOT A CURRENT ABSENCE — and the recovery instruction is what fossilises it
(2026-07-31, `exists_rationalCuspSectionsX1_field`.) A task prompt for this leaf ranked its
second route as "needs the Tate uniformisation, which was DELETED as free-floating in
`52297bf2` — recover with `git show 52297bf2...^:<path>`". Every clause of that is checkable and
the first two are TRUE: the sweep really did delete `TateCurveConstruction` (1551 lines) and
`TateUniformization` (2890 lines) on 2026-07-18. The conclusion is false. Both were rebuilt and
are in the tree today at **16 000 lines across six modules**, and `TateSepClosure` is
`public import`ed by `FreyCurve/Semistable.lean` and `Modularity/Interface.lean`, so the whole
chain compiles on every build. One `ls` of the directory refutes it.
**The recovery instruction is what makes this worse than an ordinary stale claim.** "Deleted —
recover it with `git show`" reads as *already checked, and here is the workaround*, so the reader
runs the `git show` rather than the `ls`. It also carries a citation, which is the shape doctrine
already flags as self-certifying: the commit is real, the diff is real, and the claim is still
wrong about the present. **A deletion commit is evidence about a moment, and this tree re-adds
deleted material routinely** — the free-floating sweep deletes what has no consumer *yet*, and
the same theory comes back when a consumer appears.
So: **before quoting any absence, `ls` the directory and `grep` the tree at HEAD.** And when the
absence turns out to be stale, do not just fix your own note — the false claim propagates through
prompts, so correct it where the next agent will read it (the declaration's docstring), and say
what IS there.
The correction changed the whole cost estimate, and a four-line scratch settled it in one
`lake env lean`: for a bare `(K : Type) [Field K]`, `TopologicalSpace K⸨X⸩`, `CompleteSpace K⸨X⸩`
and `WeierstrassCurve.tateCurve q : WeierstrassCurve K⸨X⸩` all elaborate, with no hypothesis on
`K` and no characteristic assumption — the in-tree Tate curve is defined over
`{k : Type*} [Field k] [TopologicalSpace k]` by `tsum`s, not over a characteristic-zero local
field. So the route is to INSTANTIATE an existing theory, not to build one. **"Needs a theory
nobody has written" and "needs an instantiation nobody has run" are different dispatches, and
only the second is one an agent can finish.**
The same scratch also located the real blocker one layer lower than the mathematics predicts:
the first missing instance is `ValuativeRel K⸨X⸩` — mathlib has `Valued K⸨X⸩ ℤᵐ⁰` and a
`Valued`-to-`ValuativeRel` bridge and nobody has connected them — not local compactness, which
is the *second* obstruction and only bites over infinite residue fields. **A negative instance
probe is worth writing even when you are sure of the answer**: "which instance fails FIRST" is a
different question from "which hypothesis is mathematically false", and it is the one that sizes
the next task.
