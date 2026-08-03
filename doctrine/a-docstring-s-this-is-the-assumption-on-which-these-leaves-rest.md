## A DOCSTRING'S "THIS IS THE ASSUMPTION ON WHICH THESE LEAVES REST" IS AN UNOWNED LEAF — AND IF TWO LEAVES REST ON IT, IT IS OWED TWICE
(2026-08-02, `flt-lean-314`, `ModularCurve/X0.lean`'s integral-model cluster.)  A
2026-07-31 cut replaced one citation by four smaller statements and wrote a long,
careful, entirely correct justification for the split.  Its subsection comment
ended:
> With all four, `XZ` is a normal proper integral model … two such are birational,
> normal and proper, so the identity on the dense open `YZ` extends to an
> isomorphism … **That uniqueness argument is the assumption on which the two
> geometry leaves rest**; it is not formalised here, and the check that would
> refute it is …
**That sentence is not a caveat. It is a leaf with no name, no owner and no
`sorry`** — and while it stayed unnamed each of the two leaves resting on it was
STRICTLY HARDER THAN THE CITATION IT ADVERTISED.  Igusa / Deligne–Rapoport /
Katz–Mazur prove smoothness and irreducibility of the model THEY construct; a
prover of `smoothOfRelativeDimension_of_isX0NormalProperModel`, which quantifies
over EVERY model, owed the citation *and* the uniqueness theorem — and the
uniqueness half was owed TWICE, once inside each of the two geometry leaves,
named by nothing and shared by nothing.
This is the already-recorded "a leaf stated for EVERY representing object cannot
consume its own citation" shape, with a twist worth its own entry: there the
bridge was FREE (Yoneda) and simply unwritten; here the bridge is EXPENSIVE and
the docstring knew it, said so, and still left it unnamed — so the cost was
invisible to every scan, duplicated across two leaves, and would have been paid
twice or (more likely) never.
**The check costs one grep over leaf docstrings**, and every hit is a candidate
for promotion to a named leaf:
    grep -n 'is the assumption\|is not formalised\|rests on\|we may assume\|at most one solution'
**The repair, and the trap inside it.**  The obvious fix — restate the citation
as a bare existential, "SOME model is smooth and connected" — is right about the
shape and **kills the cheap half of the cut**, because that existential SUBSUMES
the construction leaf (`exists_isX0NormalProperModel_specLoc`), leaving it with
no consumer, i.e. free-floating, which this project forbids.  Give the citation
leaf the construction leaf's OUTPUT as a hypothesis instead:
    theorem exists_smooth_connected_of_isX0NormalProperModel …
        (_M : IsX0NormalProperModel N xstr ystr jZ) :
        ∃ XZ' xstr' jZ', ∃ _ : IsX0NormalProperModel N xstr' ystr jZ',
          SmoothOfRelativeDimension 1 xstr' ∧ GeometricallyConnected xstr'
`_M` is never used by the intended proof and that is the point: it keeps the soft
construction CONSUMED and separately dispatchable.  Hold the shared object
(`ystr`) FIXED across the conclusion, or the uniqueness leaf has to compare two
coarse spaces as well as two models.
**Report the accounting plainly: `3 → 3` open leaves plus two proven
declarations.**  A count-neutral recut has to be argued on what is LEFT in each
leaf — here, that no leaf hides an obligation, that the uniqueness is owed once
instead of twice, and that all three survivors are lookup-able (Nagata plus
relative normalisation; uniqueness of normal proper models, Liu 8.3 / Stacks
0C5R; Igusa).
**FALSITY AUDIT FOUND WHILE WRITING THE NEW LEAF, and it is the shape to expect
from a uniqueness statement: the degenerate level breaks it.**  At `N = 0` the
coarse space is EMPTY, so `finite_compl` degenerates from "the cusp locus is
finite" to "the model is a finite SET", and then both `Spec ℤ_(ℓ)` (structure map
the identity, proper) and `Spec 𝔽_ℓ` (structure map a closed immersion, proper)
satisfy every field of the structure — integral, integrally closed stalks, the
empty scheme open-immersed, finite complement — while not being isomorphic (two
points against one).  So `0 < N` is load-bearing for TRUTH, not for the proof.
**Whenever a clause is a FINITENESS of a complement, instantiate it at the level
where the open part is empty**; that is where such a clause stops saying what it
was written to say.
Two mechanical facts, both measured in a 9-second scratch against the built
olean, and they are the whole of the new proofs:
* **`SmoothOfRelativeDimension 1` transports along an isomorphism over the base
  in three instance steps.**  An iso is an `IsOpenImmersion`, hence
  `SmoothOfRelativeDimension 0` (mathlib instance, priority 900); the comp
  instance ADDS relative dimensions; and `0 + 1` reduces to `1` definitionally.
  So `haveI : SmoothOfRelativeDimension (0 + 1) (e.hom ≫ xstr') := inferInstance`
  then `rw [← he]`.
* **`GeometricallyConnected` does NOT transport that way** — `GeometricallyConnected.comp`
  needs `GeometricallyConnected e.hom` *and* `UniversallyOpen` on both factors, and
  the first has no instance at this pin, so `infer_instance` fails on a goal that
  looks obvious.  Use `MorphismProperty.cancel_left_of_respectsIso
  (P := @GeometricallyConnected) e.hom xstr'`, which is available because
  `GeometricallyConnected` is `IsStableUnderBaseChange` and mathlib derives
  `RespectsIso` from that (`IsStableUnderBaseChange.respectsIso`, priority 900).
  **The general lesson: for a `MorphismProperty`-shaped class, reach for
  `cancel_left_of_respectsIso` before the composition lemma** — cancellation needs
  only `RespectsIso`, which base-change stability gives free, whereas composition
  lemmas here carry openness side conditions that an isomorphism does not obviously
  satisfy.
