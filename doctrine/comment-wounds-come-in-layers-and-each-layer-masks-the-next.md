## COMMENT WOUNDS COME IN LAYERS, AND EACH LAYER MASKS THE NEXT — repair to a FIXPOINT

(2026-07-31, `flt-lean-385`, on `merger` at release 27. `X0.lean` was RED with the
`maxErrors` cap of 100 reached at line 74336; five comment wounds and one truncated
declaration accounted for 18 of them and for every `Unknown identifier` in the file.)

The existing sections already say to run a nesting scan and that `depth > 0` names its
own culprit while `depth < 0` is "mostly noise". Three corrections, all measured.

**1. `depth < 0` IS THE MIRROR DEFECT, AND EACH STRAY IS ITS OWN WOUND.** A `-/` seen at
depth zero means a docstring's OPENER was dropped by the merge, so its prose sits in code
position. That is a hard parse error every time. Do not dismiss the count — print the
LINE of every stray and read the six lines above it. The tell is unmistakable: English
immediately after a `theorem`/`def` body, ending in a `-/` with no `/--` above it.

**2. THE LAYERS MASK EACH OTHER, SO THE SCAN MUST BE RE-RUN AFTER EVERY REPAIR.** Because
block comments NEST, an orphaned OPENER swallows every later delimiter, so the strays
inside its range are invisible while it stands. Here the first scan reported `depth = -5`
with two swallowed regions; fixing those two exposed **three more** strays that had been
counted as legitimate closers, and fixing one of those exposed a truncated `theorem`
header. Iterate until the scan reports `depth = 0` with an EMPTY stray list — that is the
only stable state, and it took four rounds.

**3. THE REPAIR ITSELF CAN RE-BREAK THE FILE: NEVER WRITE A COMMENT DELIMITER INSIDE A
COMMENT, EVEN IN BACKTICKS.** The note explaining the first repair spelled out the two
delimiters in a Markdown code span; the closing one ended the module comment 120 lines
early and moved the parse error to a new place. Lean's lexer knows nothing about code
spans. Write "the closing delimiter" / "the doc-comment opener" in prose.

**The three shapes seen, and the repair for each:**

* *orphaned OPENER, block still wanted* — reopen it as a `/-!` module comment and close
  it. Do this when a live docstring elsewhere cites the prose by name (one here did:
  "the `THERE IS NO FORMAL PROOF` section remains accurate");
* *foreign docstring spliced INTO another* — the inner one's `-/` ends the outer twelve
  lines early. If the inner block is a verbatim duplicate of one that still has its own
  declaration, DELETE it; if it is a section note that lost its opener, MOVE it out and
  reopen it as `/-!` before the docstring it invaded;
* *truncated declaration* — a `theorem` line followed by bare English. This is TWO
  BRANCHES ADDING THE SAME DECLARATION UNDER TWO NAMES: the merge kept branch A's
  docstring plus the FIRST LINE of A's signature, then B's docstring body (minus its
  opener) and B's complete declaration. Here that was
  `exists_gamma0Rigidification_of_rigidifiedModuli` versus
  `…_of_rigidifiedModuli_motive`, same statement, same proof. Keep the copy that arrived
  INTACT, join the two docstrings, and rename the call sites — the argument lists agree,
  because both branches gave the new parameter the same position and type.

**And check what the repair UNBLOCKS, not only what it silences.** A declaration whose
signature fails to elaborate is absent from the environment, so every later use is an
`Unknown identifier` and every theorem containing one is absent in turn — which is why
one truncated header produced `Unknown identifier RigidifiedModuliData` 2000 lines below.
Fixing it here also turned `exists_gamma0GITPresentationOver_normalModuli_zmod` from an
errored (hence `sorryAx`-tainted, hence invisible-to-every-scan) declaration back into
the proven theorem it was written as.

**Budget note for whoever inherits a red giant file**: `lean -DmaxErrors=2000
<file>` under a harvested `LEAN_PATH` elaborates all 108 k lines of `X0.lean` in about
seven minutes and gives the COMPLETE error list; the default cap of 100 stops at 70% of
the file and hides everything after it. Use `lake env printenv LEAN_PATH` to harvest, and
invoke bare `lean` — `lake env lean` resets the variable.

