## A DUPLICATE DECLARATION NAME ACROSS IMPORTS IS AN ERROR ONLY WHEN THE STATEMENTS DIFFER — otherwise one copy SILENTLY SHADOWS the other
(2026-07-31, `flt-lean-161`, measured with a four-module reproduction rather than
inferred.  This changes how every `xdup.py` report in this file should be read.)
`xdup.py`'s QUALIFIED pass is described above as finding "hard
`environment already contains …` import failures".  That is true of some of its hits and
false of others, and the discriminator is not the name — it is **what the module system
SERIALISES**:
| two modules declare the same full name | importing both |
| `theorem`, SAME statement, different proof | **silently accepted** — one shadows the other, no diagnostic |
| `theorem`, DIFFERENT statement | hard `environment already contains` |
| `def`, different body | hard `environment already contains` |
The reason is the one this file already records for a different purpose: **theorem proof
bodies are ELIDED by the module system**, so two theorems whose statements agree serialise
to the same public information and the importer sees nothing to object to.  A `def` body is
published by `@[expose] public section`, so `def`s collide on any difference.
The reproduction is four two-line modules and takes under a minute; run it before believing
any claim in this file about which names "collide":
    Fermat/Dup161/A.lean:  theorem Dup161Test.bar : True := trivial
    Fermat/Dup161/B.lean:  theorem Dup161Test.bar : True := by trivial      -- accepted
    Fermat/Dup161/B.lean:  theorem Dup161Test.bar : (1:Nat) = 1 := rfl      -- ERROR
    Fermat/Dup161/{E,F}.lean:  def Dup161Test.baz : Nat := 1 / := 2         -- ERROR
**Two consequences, and the second is the dangerous one.**
* **A QUALIFIED `xdup.py` pair is a HYPOTHESIS about a build failure, not a build failure.**
  Confirm it by importing both modules in a scratch and reading the error, before dropping
  an import or renaming anything on its authority.  Release 31 dropped `X0.lean`'s import of
  `Mathlib/AlgebraicGeometry/CurveDivisorDegree.lean` naming
  `AlgebraicGeometry.Scheme.ord_one` and `Scheme.ord_inv` as the collision; both have the
  SAME STATEMENT in both modules, so neither collides, and importing both is green.  The
  collision release 29 really hit was `AlgebraicGeometry.divDegree_eq_zero`, whose two
  statements differed by an `f ≠ 0` — and release 29 had already fixed it by renaming.  So
  the release-31 note was describing a wound that had been closed two releases earlier.
* **SILENT SHADOWING IS WORSE THAN THE ERROR, because nothing reports it.**  Two branches
  that prove the same statement under the same name produce a tree where one proof is simply
  discarded at import time — no warning, no duplicate-declaration error, and `#check` shows
  a single declaration.  The FRONTIER SCAN still counts both, because it reads SOURCE; so a
  leaf can be silently deduplicated by the linker and double-counted by the release
  invariant at the same time.  The instrument that sees it is `xdup.py` (either pass) or
  `dupstmt.py`, never the compiler.
**And the corollary for reading this file: an "environment already contains" note that names
its colliding declarations is evidence about the day it was written.**  Duplicate names get
renamed continuously, and a note naming the WRONG pair — as this one did — is
indistinguishable from a correct one until you run the import.  Re-run it; it costs seconds
and it is the only thing that separates a live blocker from a closed one.
