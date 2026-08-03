## A DOCSTRING THAT FORBIDS DUPLICATING ONE HALF CAN BE PRESCRIBING DUPLICATION OF THE OTHER
(2026-07-31, `flt-lean-14`, closing `det_galoisRep_five_eq_one_of_mem_localInertiaGroup`
in `FreyCurve/IsogenySignature.lean` — the whole leaf was six lines of tactic.)
That leaf's route note is unusually careful. It splits the content in two, says
where each half lives, and ends with a bolded prohibition:
> **The second half is ALREADY PROVEN IN THIS FILE**, as
> `cyclotomicCharacterModL_eq_one_of_mem_localInertiaGroup_of_ne` … A prover has
> two honest routes: hoist that theorem above this point, or state and prove
> `det ρ̄₅ = χ₅` on all of `Γ ℚ` above this point and consume it here — **the
> second is strictly more useful**, since the determinant identity is wanted
> elsewhere too. **Do not restate the unramifiedness half as a new leaf: that
> would duplicate a proven declaration.**
The prohibition is right. **The recommendation is the duplication it forbids,
one half over.** `det ρ̄_p = χ̄_p` on all of `Γ ℚ` is
`WeilPairing.det_galoisRep_eq_cyclotomic`, PROVEN 2026-07-17 and reached by a
`public import` at line 98 of the very file — the file's own header comment even
names it. Taking the "strictly more useful" route means writing a second copy of
an imported theorem; the route the note ranks second is the only one that adds
anything.
**The asymmetry has a cause, and it is what makes this predictable rather than
careless: the author checked the FILE for one half and did not check the IMPORT
CONE for the other.** An in-file `grep` is what a route note's author naturally
runs while writing the note, and it is exactly the check that cannot see the
imported half. So the note reads as thorough — it demonstrates in-file
awareness — while being blind along the one axis that mattered.
**The check, before following any "state and prove X above this point"
instruction:**
    grep -rn '<the conclusion, or the concept>' --include=*.lean Fermat/   # WHOLE tree
    grep -n '^public import' <your module>                                 # then: is it in your cone?
Both, in that order, and grep for the CONCEPT rather than the name you were
about to give it — the existing copy is called something else. Same family as
`NOT IN MATHLIB, NOT IN ~/cs/FLT — CHECK YOUR OWN IMPORT LIST FIRST` above, with
the twist that here the docstring is not claiming an absence at all: it is
telling you to *write* something, which reads as a work order rather than as a
claim to verify.
**And the route a note ranks LOWER may be the whole of the remaining work.**
With the determinant identity free, everything left was declaration order: the
unramifiedness half sat ~1150 lines below the leaf. Hoisting it (with its
ring-theoretic core, 234 lines, verified as a pure move by sorting the old and
new file and diffing — empty) plus six lines of tactic closed the leaf. Cost:
one afternoon against the note's own estimate of a new global theorem.
Three riders, all cheap and all of which decided something here:
* **A hoist is safe only if nothing between the two positions is in the moved
  block's cone, AND there is no scope boundary in between.** The second half is
  the one people forget: `grep -n '^\(section\|end\|namespace\|open\|variable\|
  set_option\|attribute\)'` over the jumped range must be EMPTY, or the moved
  declarations silently change what is in scope for them.
* **Elaborate the proof in a scratch module that `public import`s the target's
  own module BEFORE doing the hoist.** Module imports have no declaration order,
  so the scratch sees the below-you theorem and tells you in seconds whether the
  mathematics works — 10 s here against ~20 min for the real file. The hoist is
  then a separate, purely mechanical step whose only failure mode is order.
* **`Fact` instances are proof-irrelevant but not syntactically equal**, so
  state the bridge as a `have` with the type written out and close it by
  `exact`/term-mode rather than by `rw` at the instance. Here
  `(cyclotomicCharacterModL 5 σ : (ZMod 5)ˣ) = 1` typechecked directly against a
  theorem whose instance argument is a literal `⟨Nat.prime_five⟩`, where a
  rewrite through the ambient `Fact` instance would have been the usual
  printed-pattern-equals-printed-target failure.
