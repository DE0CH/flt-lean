## A ROUTE AUDIT NEVER CHECKS DECLARATION ORDER — and that is a whole blocking axis

(2026-07-31, flt-lean-210, found by trying to walk a route the file certified as open.)

Every audit shape this project writes — ROUTE AUDIT, ATOMICITY AUDIT, CUT-OBSTRUCTION AUDIT —
reasons about *mathematics* and about *what exists in the tree*. None of them reasons about
**where in the file it exists**, and in a 31k-line module that is a live, independent way for a
leaf to be unattackable.

`exists_framedGaloisRep_descent_hilbertTraceSubring_of_isWeaklyUniversal`
(`HardlyRamified/HilbertModularity.lean`) carried a section headed "ROUTE OBSTRUCTION FOUND —
REPAIRED. THE BINDER IS NOW ON THIS NODE", ending "**The route described below is therefore
AVAILABLE, and a prover dispatched at this leaf now has one**", and the consumer's summary agreed:
"The route is available; the leaf is attackable." The binder repair was real and the mathematics
was right. **Every declaration the route spends sits ~1000–2000 lines BELOW the leaf**, so Lean
forbids the appeal — and restating any of them above it would duplicate a live declaration, which
is worse. The docstring even records the block correctly for ONE of those declarations
(`exists_framedGaloisRep_hilbertTraceSubring`, "blocked mechanically: both live BELOW this point")
without noticing it applies to the whole route.

So: **before certifying a route as available, `grep -n` the line number of every declaration it
spends and compare it with the leaf's own.** It costs one command. And when you record a route,
record the line numbers, because they are the part of an audit that a reader cannot re-derive from
the mathematics.

Two corollaries:

- **The repair is a RELOCATION, and relocations are the worst shape for a merge** (a ~950-line
  block move conflicts with any concurrent edit inside it). So measure it, write the recipe into
  the docstring, and queue it as its OWN commit touching nothing else — do not attempt it while
  the file has another owner. The measurement that makes it safe is one grep: the names declared
  in the moved block, searched for *in code* across the range it moves over.
- **"Blocked, it is another module's region" is the same error one level up, and it is usually
  wrong about CUTS.** The same file declined its own next cut on the ground that the repair lives
  in `Modularity/MoretBailly.lean`. Proving the sub-leaves does live there; **stating** them cost
  nothing, because that module is a `public import` and every name in their signatures was already
  in scope. The cut was taken from the consumer's file, no other file was touched, and it exposed
  a second obstruction nobody had recorded. This is CLAUDE.md's "STATING a theory is not PROVING
  it" in its commonest disguise: an obstruction to the PROOF written down as an obstruction to the
  CUT.

