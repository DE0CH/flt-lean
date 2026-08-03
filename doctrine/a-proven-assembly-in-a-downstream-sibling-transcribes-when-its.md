## A PROVEN ASSEMBLY IN A DOWNSTREAM SIBLING TRANSCRIBES WHEN ITS INPUTS ARE UPSTREAM OF YOUR LINE
(Same task, and it is the other half of what closed the leaf.)
The standing rule is that a theorem in a file which IMPORTS yours cannot be
cited. True, and it stops most readers there. **What can still be true is that
every declaration the downstream proof CONSUMES is upstream of your own line** —
and then the proof transcribes verbatim, as text, at your site.
`X1.lean`'s `exists_nonconstant_toAbelianScheme_of_hasNoFibreAffineLine` is
PROVEN and is exactly the nonconstancy assembly this leaf needed. `X1` imports
`X0`, so it is uncitable. Its eight inputs — `exists_relPicZero`,
`IsRelPicZeroOf.isAlbaneseOf`, `IsAlbaneseOf.isJacobianOf`,
`mono_ajHom_of_hasNoFibreAffineLine`, `IsJacobianOf.{ajHom, aj_val,
injective_aj_of_mono}`, `not_isIso_of_smoothOfRelativeDimension_one` — are at
`RelativePicard`, 55401, 54171, 63207, 37309, 37325, 37349 and
`CurveCompactification`. Every one is above 63945. So the twelve-line proof
pasted in and compiled first try.
**The check is one `grep -n` per input, comparing LINE NUMBERS with your own** —
the same declaration-order arithmetic this file already prescribes for a hoist,
run in the other direction and for a different purpose: not *may I move this*,
but *may I re-derive it where I stand*.
**Prefer INLINING the proof to hoisting the theorem.** A hoist has to delete the
downstream copy, which is a signature change with call sites you did not audit,
in a file with concurrent editors — the highest-conflict edit there is. Inlining
touches only your own region and creates no duplicate. Hoist only what you cannot
inline: here that was one genuinely reusable lemma
(`X1.hasNoFibreAffineLine_baseChange`), copied under a DIFFERENT name with a
docstring saying which copy should survive and the deletion recipe on it, per the
standing "copy it, deliberately" rule.
**And when you are already in the neighbourhood, check the downstream sibling for
a DUPLICATE OF THE THING YOU JUST USED.** `X1` also carried a `sorry` whose
statement is byte-identical to the proven `WeilRestriction` theorem, in a module
`X1` itself imports and whose import comment in that very file says "Stated and
PROVEN there". It closed by a one-line delegation, `−1` leaf for two lines. No
scan could see it: the two names differ by a namespace, so `xdup.py`'s qualified
pass and `check-dup` are silent; both copies emitted honest `sorry` warnings; and
`dupstmt.py`'s default scope is sorried declarations, which the proven copy is
not. **A duplicate whose two copies are one PROVEN and one `sorry` is invisible to
every instrument in this repository**, and the only thing that finds it is having
just read both.
