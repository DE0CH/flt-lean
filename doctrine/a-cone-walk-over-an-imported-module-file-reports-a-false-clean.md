## A CONE WALK OVER AN IMPORTED `module` FILE REPORTS A FALSE CLEAN — and the false clean reads as "the circularity has lifted"
(2026-07-31, `flt-lean-107`, release 33, on
`Modularity/Interface.lean`'s strong-multiplicity-one leaf.)
This file already says that `#print axioms` must be appended to the file that
DECLARES the name, because the module system elides imported proof bodies. The
same elision breaks the other measurement this project relies on, and there it
is far more dangerous, because the failure is SILENT and its output is a
positive result.
`eq_of_isWeightTwoNewform_sub_degeneracyOp_one_mem_oldSubspace` carries a
CIRCULARITY WARNING: nine named declarations, up to
`exists_galoisRep_charFrob_of_weightTwoNewform`, are its transitive CONSUMERS,
so no Galois representation this file attaches to a newform may be used to prove
it. The warning records the method that established it — *"a cone walk over
proof TERMS, run from a plain-import (non-`module`) file — a `module` file
exports no theorem bodies and reports a false clean, which is a trap this
project has been caught by before"* — together with cone sizes of 68 950–123 009.
**Run exactly that recipe today and every one of the nine comes back
`hits []`, including the POSITIVE CONTROL**, which calls the parent by name in
its own proof. Cone sizes come out ~4 900 instead of ~69 000.
The recipe is not wrong about the phenomenon and it is wrong about which file's
module-ness matters. **It is the IMPORTED file's**: `Interface.lean` is itself a
`module` (line 134), so `ConstantInfo.value?` is `none` for every theorem it
exports and the walk stops at the statement, whatever the importing file looks
like. `import all` does not help. Since the docstring's own control is inside
the elided file, the control fails silently too — a check designed to catch this
exact failure cannot catch it.
**What the false clean would cause is not a wasted grep but a wasted route.** A
reader reproducing the recipe concludes the consumers are independent, takes the
Chebotarev + Brauer–Nesbitt route the docstring describes as available-but-
circular, and builds a proof of the leaf out of theorems that rest on it.
**The method that works costs seconds, needs no build, and needs no oleans:
build the call graph from the SOURCE.** Strip comments (nested block comments —
this tree's docstrings quote Lean constantly), attribute every token to the
enclosing declaration by walking back to the nearest declaration header, and BFS
the reverse edges. Nineteen edges came back with line numbers, and each one was
eyeballed as a genuine application in a proof body rather than a mention in a
statement. Two riders:
* it only sees ONE file, so it is a complete answer exactly when the chain is
  in-file — which is how these clusters are built, and is checkable by grepping
  the endpoints;
* tokenise with `isalnum() or c in "_'."`, never a unicode range
  ([[lean-identifier-regex-swallows-brackets]]), and take the whole declaration
  block including its signature, so the graph OVER-approximates: a hit must then
  be confirmed by reading the line, and a MISS is already conclusive.
The alternative, when the chain crosses files, is to append the `run_cmd` cone
walk to the END of the declaring file — the same rule `#print axioms` already
obeys — and pay one elaboration.
