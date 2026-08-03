## A SHORT-NAME DEPENDENCY REPORT IS A HYPOTHESIS — THE REFUTING GREP IS FOR THE QUALIFIED NAME
(2026-07-31, `flt-lean-11`, on the `IsBaseChangeOfGamma1` relocation.  The task's
own premise turned out to be one of these, and so did the verdict it was written
to overturn.)
Every dependency scanner in this tree — `flt-cyclecheck.py`, `flt-hoistcheck.py`,
`tools/merge/frontier.py`, `xdup.py`'s last-component pass — matches on the SHORT
name, and every one of them says so in its docstring, correctly, as *"the safe
direction: a false cycle costs a read and a missed one costs a build"*.  That
accounting is right about the SCAN and wrong about what happens next, because
nobody re-reads the scan.  **A `CYCLE via …` line gets copied into a docstring as
prose, and prose does not carry the word "approximately".**
Measured here.  `flt-cyclecheck.py` on the `MazurIsogenyPrimeJ` tail reported two
cycles into modules that import `X0.lean`.  Both were false, and the four names
they turned on are among the most common suffixes in the library:
| reported | what the block really contains |
|---|---|
| `Fermat.IsBaseChangeOfGamma1.refl` | `Equiv.refl` |
| `Fermat.IsBaseChangeOfGamma1.comp` | `RingHom.comp`, `Function.comp`, `Polynomial.C.comp` (8 sites) |
| `Fermat.IsBaseChangeOfGamma1.along_injective` | the block's OWN `MazurIsogenyPrimeJ.IsEllipticIsoOf.along_injective` |
| `GaloisRepresentation.Modularity.val_neg` | `Units.val_neg` |
**The decisive check is one command, it needs no build, and it is a grep for the
QUALIFIED name — or for the TYPE the declaration hangs off — in the source
module, not another run of the scanner:**
    grep -c 'IsBaseChangeOfGamma1\|Gamma1Datum\|PointOfExactOrder' \
        Fermat/FLT/FreyCurve/MazurTorsion.lean          # -> 0
Zero, across all 70 000 lines: that module never mentions the `Γ₁` moduli layer,
so the hoist it was said to block was never blocked.  Re-running the scanner
cannot discover this, because the scanner is what is wrong; and this is the same
shape as the SELF-CERTIFYING GREP already recorded above, with the tool rather
than the pattern supplying the false confidence.
**The rule, and it is cheap: a scanner's POSITIVE findings are leads, not
results.**  Its NEGATIVE finding (`NO CYCLE`) is the trustworthy half, because the
matcher over-approximates.  So:
* **before costing work off a `CYCLE`/`hit`/`duplicate` line, refute it by name.**
  One grep per hit.  A hit on a name of four or five characters is a lead with a
  low prior;
* **before WRITING such a verdict into a docstring, say which check you ran.**
  "`flt-cyclecheck.py` reports a cycle via X" and "the block references
  `Foo.bar`, grepped 2026-07-31" are different claims and only the second is worth
  anything to the next reader;
* **and expect the failure to compound.**  `flt-hoist-genusone.py`'s docstring
  names a `NeronModel.lean` cycle as the reason only the genus-one branch could
  travel.  That cycle is also gone — it was traced through leaves that have since
  been proven by other routes, and an open leaf's body contributes no
  dependencies.  So a stale scanner verdict and a stale *frontier* verdict were
  stacked on top of each other, each individually plausible, and between them they
  kept two of Mazur's Theorem 1 leaves looking unreachable for days.
`flt-cyclecheck.py` now prints, under every hit, the closure declaration and the
SOURCE LINE the short name actually matched on, plus a footer saying to read them.
That turns the five-minute investigation above into a glance:
      28200  GaloisRepresentation.Modularity.val_neg   (matched on the short name 'val_neg')
             first use: …/MazurTorsion.lean:38319  in …eq_two_of_stableCyclic_autMap_stable_quartic
             | (by rw [Units.val_neg, ← hσu]) g
**Generalise it to the other scanners when you next touch one.**  A scanner that
reports a name should report the line it matched; the cost is ten lines of Python
and it is the difference between a lead and a rumour.
### The relocation itself, and why it was still worth doing
The premise being false does not make the move wrong, and the reasoning is worth
copying because "the obstruction is not real" is a common mid-task discovery.
`Fermat.{RelPoint.ofSection, PointOfExactOrder, Gamma1Datum, IsBaseChangeOfGamma1}`
and the first `namespace IsBaseChangeOfGamma1` block moved from `X1.lean` into
`X0.lean` anyway, because:
* it is a **pure reordering** — verified by the line-multiset receipt below — so
  its risk is bounded by one build, not by a proof;
* the `Γ₁` base-change calculus now sits beside the `Γ₀` one it mirrors, three
  lines below the `RelPoint.transport` API both run on;
* and it removes the *instrument-visible* obstruction, so the next agent to run
  the scanner does not read `CYCLE via …X1` and conclude, for a second time, that
  a hoist is blocked when it is not.
Two mechanical notes.  **`namespace Foo` is not a usable anchor when the file
reopens it** — `X1.lean` opens `namespace IsBaseChangeOfGamma1` three times, and
only the first block moved; anchor on a unique interior line and derive the
boundary from it, asserting what the boundary line must say.  And **audit the
direction words in the MOVED text, in a separate commit from the move**, so the
`sort`-and-`diff` receipt on the move stays clean: two sentences here became
self-referential (`the Γ₁ transcription of X0.lean's …`, now in `X0.lean`) and one
`below` came to point across a file boundary.
