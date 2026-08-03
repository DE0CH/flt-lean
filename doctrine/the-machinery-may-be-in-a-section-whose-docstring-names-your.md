## THE MACHINERY MAY BE IN A SECTION WHOSE DOCSTRING NAMES *YOUR LEAF* AS ITS CONSUMER
(2026-08-01, `flt-lean-179`, on the first main theorem of complex multiplication in
`FreyCurve/MazurTorsion.lean`.  Cost: ~250 lines re-derived from scratch before the
grep that found the original.)
This file already records, in several shapes, that a "MISSING MACHINERY" paragraph
is reliable about ABSENCE and unreliable about STRENGTH.  Here is the sharpest and
most embarrassing form of it, because **I wrote the false paragraph myself, in the
same run, and it was false the moment it was written.**
Cutting `minpoly_eq_of_isCMJInvariantOfRel` produced a Galois-stability leaf, and I
gave it a route note ending:
> **WHAT IS MISSING FROM THE TREE, and it is a construction rather than a theory.**
> mathlib's `WeierstrassCurve.Affine.Point.map` moves points between BASE CHANGES of
> one curve over a fixed subring; here `W` and `W^σ` are genuinely different curves
> over `ℚ̄`, so that declaration does not apply and the coordinatewise map has to be
Every clause about MATHLIB is true, and it is exactly what makes the conclusion
convincing.  The conclusion is false: the whole transport — `Affine.Point.mapRingHom`,
`Affine.Point.mapRingEquiv`, `conjHom`, `IsRationalMap.transport`,
`IsIsogeny.transport`, `isRationalMap_conjHom_iff`, `isIsogeny_conjHom_iff`,
`AddEquiv.conjAddMonoidEnd` and `End.mapRingEquiv` — is PROVEN in
`Fermat/FLT/EllipticCurve/Isogeny.lean`, in a section called `GaloisTransport`, in a
module `MazurTorsion.lean` already `public import`s.  The leaf closed in ~25 lines.
**And the section's own docstring NAMES ITS INTENDED CONSUMER:** *"The intended
consumer is `Fermat/FLT/FreyCurve/MazurTorsion.lean`'s `MazurCMForm.IsCMJInvariant.map`:
… the CM `j`-invariants of a fixed order are stable under `Gal(ℚ̄/ℚ)`"* — that is my
leaf, one predicate over.  So the information was not merely present, it was
addressed to me.
**THE CHECK THAT FINDS IT, and it is not a name grep.**  I did not find this by
searching for the concept; a name search fails by construction, because the author
of the machinery names it in THEIR vocabulary (`conjHom`, `mapRingEquiv`) and you
search in YOURS (`IsCMJInvariantOfRel`, "conjugate curve", "Galois stability").
What found it was one command, run for an unrelated reason — listing the STRUCTURE
of the module I was about to add the machinery to:
    grep -n '^namespace \|^end \|^section \|^variable ' <the module you would extend>
`end GaloisTransport` is a two-word summary of 250 lines.  **A section name is a
concept name, and a module's section list is the cheapest index of its contents
there is.**  Run it on the file you are about to extend, BEFORE you extend it — and
read the section's docstring, which in this development routinely says who it is for.
* **A memory note's absence claim is dated exactly like a docstring's.**  The
  `flt-lean-159` CM survey in this fleet's memory priced this transport at "a real
  ~200-line build in `Isogeny.lean`.  Price it before promising it."  That was true
  when written and had been built by the time I read it.  I quoted it as current.
* **The tell I ignored**: my own note said the natural home for the missing
  machinery was "`Fermat/FLT/EllipticCurve/Isogeny.lean`, beside `endSubring`".  When
  you can name the file the machinery belongs in, you are one `grep` from finding out
  whether it is already there, and that grep costs a second.  Naming the home and not
  looking in it is the specific failure.
Corollary for whoever writes such a paragraph: say which trees you searched and with
what command, and search the destination file you just named.  A route note that says
"X has to be built" without a quoted command is a guess, and the next reader — who may
be you, twenty minutes later — will act on it.
