## A docstring that narrates a statement change beside an unchanged statement is a seam marker

(Release 39, 2026-08-03.) The last two class-7 seams of the 387-branch batch
were found not by reading error lists but by reading the DOCSTRING of the
erroring declaration:

* `ModThree.lean`'s `exists_relArtinAuxiliaryNumberField_ray_class` carried a
  2026-08-01 audit paragraph reading "The value field moved from `Dickson.K 3`
  to a variable `KK`" — directly above a signature that still read
  `χ : Γ F → Dickson.K 3`. One branch generalised the cluster's statements to
  `KK` (docstrings and the KK-generic consumer landed); a parallel branch
  proved the pair at the old `Dickson.K 3` type (proofs landed). The merge
  kept the old signatures beside the new docstrings, and the only compile
  error was a universe mismatch two consumers away.
* `HilbertModularity.lean`'s callers of
  `exists_framedGaloisRep_baseChange_hilbertTraceSubring` still passed the
  exploded eight-argument list (`𝒟.ρ 𝒟.isHilbertHardlyRamified.det 𝒟.π …`)
  after the callee had been re-signed to take the whole
  `HilbertDeformationDatum` — again with the callee's docstring describing
  the new shape.

The repair rule both times: MAKE THE SIGNATURE MATCH ITS OWN DOCSTRING, then
fix the destructurings/call sites mechanically. The docstring is the record
of intent (it was re-audited when the statement changed, per this project's
audit discipline), so when signature and docstring disagree after a merge,
the signature is the stale half — the opposite of the usual "comments lie,
code doesn't" prior, and exactly because this repo's docstrings carry dated
faithfulness audits.

Detector, cheap enough to run on any file that errors after a merge:

    grep -n 'moved from\|now takes\|renamed to\|restated\|STATEMENT changed' <file>

and check each hit's declaration actually reflects the narrated change. A
conjunct-count mismatch in an `obtain` pattern (`hnorm` silently swallowing
`(normality) ∧ w ∈ H` as a nested pair) is the same seam one consumer down:
grep the callee's conclusion for `∧`-count when an anonymous-constructor
argument mismatches.
