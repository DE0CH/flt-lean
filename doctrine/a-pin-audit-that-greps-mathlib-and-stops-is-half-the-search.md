## A PIN AUDIT THAT GREPS MATHLIB AND STOPS IS HALF THE SEARCH — GREP THE PROJECT TOO
(2026-07-31, `flt-lean-255`, cutting `exists_isCMJInvariant_ne_of_not_equivalent`.)
The CM SURVEY written for this cluster the same day is careful, explicitly says every line
was `grep`ed rather than recalled, and states: *"No lattices in `ℂ`, no analytic `j`-function,
no uniformisation. `Mathlib/NumberTheory/ModularForms/` has Eisenstein series, `Δ`, the `η`
function and `q`-expansions — and no `j`."* Every word of that is **true about mathlib and
false about this repository.**
`Fermat/FLT/Mathlib/NumberTheory/BinaryQuadraticForm.lean` — which `MazurTorsion.lean` already
`public import`s — carries a 4000-line Heegner–Stark development containing
`Fermat.BinaryQuadraticForm.Heegner.jInvariant : ℍ → ℂ` (`= E₄³/Δ`, numerically checked against
PARI's `ellj`), and beside it, both **PROVEN**:
* `jInvariant_smul` — `j(γ • z) = j(z)` for `γ ∈ SL₂(ℤ)`;
* `isIntegral_jInvariant_of_quadratic` — `j(z)` is an algebraic integer whenever `z ∈ ℍ`
  satisfies a nontrivial integral quadratic relation.
Those two are most of the analytic input a CM leaf needs. With them the leaf cut into a PROVEN
form-to-`ℍ` dictionary plus two sharply-stated leaves, one of which
(`j` is injective on `ℍ/SL₂(ℤ)`) is a pure mathlib-shaped modular-function statement.
**Why the miss is systematic rather than careless.** A survey asks "does the PIN have X?", and
its natural instrument is `grep .lake/packages/mathlib`. But this tree vendors and builds its
own theory constantly, and the module that has your missing theory is often one your target
ALREADY IMPORTS — filed under a name that has nothing to do with your subject. `jInvariant`
lives in a file called `BinaryQuadraticForm.lean`, under `namespace Heegner`, because it was
built for the class-number-one problem. No subject-matter search finds it.
So the standing check, and it costs one command:
    grep -rn "<the object>" Fermat/ --include=*.lean       # BEFORE concluding "not in the pin"
and read the target module's own import list — a theory you can cite for free is one that is
already in your cone. This is the same lesson as *"Missing machinery may be DOWNSTREAM"*
(a theorem proven in a file that imports yours) pointed the other way: **UPSTREAM, in a file
yours already imports, under somebody else's heading.**
Corollary for absence claims in docstrings: a `MISSING MACHINERY` list that cites only mathlib
is evidence about mathlib. Say which trees were searched, or the next owner will believe it
covered all of them — and mark the item struck rather than deleting it when it turns out to be
wrong, so the next survey learns the failure mode and not just the fact.

