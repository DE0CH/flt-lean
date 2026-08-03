## A `local instance` UPSTREAM is invisible DOWNSTREAM — even when its term is in your goal

(2026-07-31, `MazurTorsion.lean`, one build cycle.) `WeilPairing.det_galoisRep_eq_cyclotomic`
has `algebraMap ℤ_[p] (ZMod p) (…)` on its right-hand side. `rw` it into a downstream goal
and that term appears there, fully elaborated. Then write `algebraMap ℤ_[5] (ZMod 5)`
yourself — as `WeilPairing.lean` itself does two lines from the end of that very proof — and
you get:

    failed to synthesize instance of type class
      Algebra ℤ_[5] (ZMod 5)

for a class the goal is visibly displaying. The instance is
`noncomputable local instance instAlgebraPadicIntZModWeilPairing`
(`Fermat/FLT/EllipticCurve/WeilPairing.lean:115`). **`local` scopes the ATTRIBUTE, not the
declaration**: the constant is exported and travels inside any imported statement that
mentions it, but instance SEARCH cannot find it after the import. So the term is present and
unwritable at the same time, and a proof step that is legal in the defining file is illegal
one import away. Copying a working tactic block out of the upstream file is exactly how you
hit this.

Three fixes, cheapest first:

1. **Never write the class's `algebraMap`/operation yourself.** Here the instance is
   `RingHom.toAlgebra PadicInt.toZMod`, so `algebraMap ℤ_[5] (ZMod 5)` and `PadicInt.toZMod`
   are DEFEQ and `exact` converts silently: `exact (…).symm.trans h` closed it where a
   `rw [show algebraMap … = PadicInt.toZMod from rfl]` could not even elaborate.
2. `attribute [local instance] WeilPairing.instAlgebraPadicIntZModWeilPairing in` before your
   declaration — needed if you genuinely must MENTION the operation (e.g. to `rw` at it,
   which needs a syntactic match against the goal's copy, so re-declaring your own
   `local instance` with the same body is NOT equivalent and may fail to match).
3. Only if it is wanted repeatedly: promote it upstream to a real instance.

**The diagnostic tell, since the error message points at the wrong thing:** a "failed to
synthesize `C X Y`" for a class that OCCURS in the goal you are staring at means a local or
scoped instance upstream, not a missing one. `grep -n 'local instance\|scoped instance' <the
upstream file>` before hunting mathlib for something to import.

