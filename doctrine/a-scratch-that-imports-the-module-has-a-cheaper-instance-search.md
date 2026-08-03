## A SCRATCH THAT IMPORTS THE MODULE HAS A CHEAPER INSTANCE SEARCH THAN THE MODULE ITSELF

(2026-08-01, `flt-lean-239`, `HyperellipticJacobian.lean`.)  The scratch-module rule is the
biggest throughput lever in this fleet and it has a failure mode that costs exactly one full
build.  530 lines developed against a scratch that `public import`s the target module
compiled in **6 seconds** and, pasted verbatim into the target, failed with

    failed to synthesize  Nontrivial (D.residue v)
    (deterministic) timeout at `typeclass`, maximum number of heartbeats (20000) has been reached

The mathematics is identical, the names are identical, the notation scope is identical.
What differs is that **inside the defining module every instance declared above your block
is in the LOCAL environment, while through an import they arrive already elaborated** — so
`synthInstance` has strictly more to chew on in the real file, and a `simp` call that is
instant in the scratch can trip the 20 000-heartbeat cap there.

The standing warnings say a scratch proves nothing about the target's import surface or
notation scope, and that it does not share the target's *unification* behaviour.  This is a
third axis and the one you will actually hit: **elaboration COST**.  It has a specific tell —
the error is a heartbeat timeout rather than a real failure — and a specific cure:

    section MyBlock
    set_option synthInstance.maxHeartbeats 1000000
    set_option maxHeartbeats 1000000

as a SECTION-scoped option rather than ten `set_option … in` lines, one per declaration.
The neighbouring `SinglePlaceBound` section in that same file already carries the identical
bump twice, per theorem — which is the tell that the cost is a property of the FILE and not
of your proof, so scope it to the section and stop thinking about it.

Two riders:

* **Kill the expensive search as well as raising the cap.**  The failing step was
  `ext z; simpa using <lemma>`; replacing it with `ext z; rw [LinearMap.mem_ker,
  Submodule.mem_comap]; exact <lemma>` removes the search entirely.  A bare `simpa` in a
  file this size is where the budget goes; name the rewrites.
* **A failed `lake build` DELETES the target olean, so your scratch loop dies with it**
  (`object file … does not exist`, which reads like a torn `.lake`).  Restore it from
  `~/.flt-release-lake/build` — copy the WHOLE `<Module>.*` set, not just `.olean` — and the
  6-second loop is back.  That is what let the fix be tested in seconds instead of in
  another ten-minute build.

### And the plan step that turned out to be free

Same leaf, worth its own line because it is the shape [[flt-leaf-cost-estimates-are-hypotheses]]
predicts.  The leaf's docstring said this half "has to know residue degrees are finite" and
budgeted that as part of its step 3.  It is a two-line corollary of a theorem already in the
file: **a uniformiser at `v` is transcendental** — an element algebraic over `K` is a unit at
every place, and a uniformiser has `ord v t = 1` — so `t⁻¹` is a transcendental element with
a pole at `v`, which is exactly what `finite_residue_of_ord_neg` consumes.  Hence EVERY place
has finite residue degree, with no hypothesis at all, and the whole
support-of-the-divisor bookkeeping the plan budgeted for disappears.  **When a plan says a
step must CARRY some finiteness, check whether the object it is about admits a transcendental
element by construction; in a function field it always does.**

