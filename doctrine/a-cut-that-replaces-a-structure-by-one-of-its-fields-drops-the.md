## A CUT THAT REPLACES A STRUCTURE BY ONE OF ITS FIELDS DROPS THE OTHER FIELDS — and the structure usually says WHY it carries them
(2026-08-01, `isOpenImmersion_equalizer_of_geomTorsionBasis` in `ModularCurve/X0.lean`.)
A standard and good move here is to restate a leaf so it stops mentioning a project
structure and takes only the FIELD its proof consumes: `FullLevelStructure n d` became the
bare fibrewise hypothesis `hbasis`, which is `geom_basis` and nothing else. That deleted the
moduli content from the statement, which is what the cut was for — and it silently deleted
`nsmul_P` and `nsmul_Q` too, which are the two fields the ONE available arithmetic input
needs.
**The structure's own docstring had already written down that they are not recoverable.**
`FullLevelStructure`'s says, in bold and with a counterexample, *"`nsmul_P` and `nsmul_Q` are
FIELDS, and they are NOT consequences of `geom_basis`"* — a paragraph added in an earlier
repair, when somebody had derived them and been wrong. A cut that keeps `geom_basis` and
drops the other two is that same error one level up, and it is much harder to see, because
nothing in the new statement mentions the structure any more.
**So: when you restate a leaf to take a field instead of the structure, read the structure's
field list and ask, per remaining field, whether the proof needs it.** The docstring beside
the fields is the cheapest place this is ever written down, and in this development a field
that is not derivable usually carries a note saying so.
**The clauses cost the caller nothing, which is the test for putting them back.** They were
`L.nsmul_P` / `L.nsmul_Q` pushed along `nsmul_pre_eq_zero`; the sole producer gained two
arguments, both call sites were untouched, and the leaf closed. Adding hypotheses can only
shrink the class of counterexamples, so the existing falsity audit transferred with a
one-sentence argument rather than a re-run.
**And record how far the derivation DOES get, because "not derivable" invites a re-attempt.**
Here the useful residue is a dichotomy anyone can check in ten minutes: reading the `∃!` at
`x = y` gives existence at `c = (1,0)`, and uniqueness splits as `a ≥ 1` — where the
uniqueness half at `x = 0` forces `(a,b) = (1,0)` — and `a = 0`, where the equation reads
`y = b·z` and nothing excludes it. So the honest consequence is *`n • y = 0` OR `y = b·z`
for some `b < n`*, dually for `z`; three of the four combinations are free, and the fourth
makes the torsion CYCLIC, which needs `#E[n]` to refute. Writing the dichotomy down is worth
more than "not derivable", because it names exactly the missing input.
### Riders, both from the same run
**A PROVEN theorem can keep a `(sorry leaf)` header AND a "not provable from what is here"
survey, and be consumerless as well.** `natCast_ne_zero_of_geomBasis` had all three. Its
survey correctly ruled out two routes — both wanting `deg [n] = n²` or invariant
differentials — and the proof beside it goes by a THIRD: `E[p]` is CYCLIC, which is the
*qualitative* shadow of the `#E[p] ≤ p` the other two wanted *quantitatively*. **When a
verdict prices a leaf off a missing COUNT, ask whether the argument needs the count or only
its qualitative consequence** (cyclic, non-trivial, proper, bounded); this development's
absence tables are reliable about the quantitative statements and have now twice missed the
qualitative one.
**A leaf blocked purely by declaration order is a hoist, and the hoist is cheap when you
measure it in both directions.** Both inputs here sat ~30 000 lines below the leaf. Moving
the leaf and its consumer cluster down is thousands of lines; moving the two inputs up is
123, and the checks are one script: the block references only names above the DESTINATION,
neither moved name occurs between destination and source, the block contains no
`namespace`/`section`/`variable`/`open`/`set_option` and no `@[simp]`/`instance`/`attribute`,
and both ends sit in the same namespace — **confirmed against the compiler, by scanning
`(← getEnv).constants` for the two names, not off a hand-rolled scope tracker, which got it
wrong first.** Then `diff <(sort old) <(sort new)` empty is the receipt that the move edited
nothing, and it goes in its own commit.
