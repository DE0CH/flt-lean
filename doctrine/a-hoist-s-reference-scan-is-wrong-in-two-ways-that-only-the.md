## A HOIST'S REFERENCE SCAN IS WRONG IN TWO WAYS THAT ONLY THE BUILD FINDS
(2026-07-31, both hit while hoisting 196 declarations out of `Interface.lean`.) The
transitive-closure scan that justifies a hoist — "the moved block references nothing outside
itself" — is the whole safety argument for the move, and a naive one is wrong twice over.
Both bugs produce the same symptom: a green scan, a red build, and an error that reads like a
missing import.
**1. A whole-token scan cannot see DOT NOTATION.** `hA.gamma0_mul` never contains the string
`IsAtkinLehnerMatrix.gamma0_mul`, so a scan keyed on declared names misses every dotted
declaration reached that way. Two theorems were left behind and the build died on
`Invalid field 'gamma0_mul': The environment does not contain …` — which looks like a
structure-field problem, not a missing move. Index dotted declarations by LAST COMPONENT, but
**also require the declaration's PREFIX to appear in the same body**: a bare suffix match on
`.one`/`.mul`/`.prod` dragged an unrelated power-series cluster (`EulerLowOne`,
`PowerSeriesLogDerivEq`) into the closure, +8 declarations of pure noise. The prefix guard works
because dot notation needs a term of that type, and the type is named in the signature.
**2. A Lean command continues onto INDENTED following lines.** This is ONE command:
    open UpperHalfPlane ModularForm Matrix.SpecialLinearGroup CongruenceSubgroup
      ConjAct
A context scanner that reads only column-0 lines silently loses `open ConjAct`, and the moved
block then fails ~12 lines later on `Unknown identifier toConjAct` — under `autoImplicit` it
surfaces as `Function expected at toConjAct`, which points at the wrong thing entirely. Join
continuation lines before classifying any `open`/`variable`/`section` line.
**And the context that must NOT come along is as important as the context that must.** At the
moved block's original position there were four `attribute [instance] …Package.addCommGroup`
lines, three `local notation`s and a `variable {p : ℕ} … {ρ : GaloisRep ℚ R V}` package, all
naming declarations that stay behind. Reproducing the `variable` line put `GaloisRep` in the new
module and broke it; dropping it is safe **because Lean includes a section variable only where it
is referenced**, and every `p`/`hp`/`hv` in the moved text was a binder of its own that shadowed
it. Check that by name before dropping, not by hope.
The mechanical purity check that IS reliable, and it costs a second: the **multiset of lines
removed from the source file must equal the multiset of moved lines**, and the only line added to
the source file must be the import. Then a comment-stripped duplicate-declaration-name scan
ACROSS both files. Neither of those can be fooled by a scan bug.
