---
name: flt-cone-walk-false-clean-on-module-imports
description: A proof-term cone walk over an imported `module` file returns "no hits" for every target, positive control included — the elision is on the IMPORTED side, so the standing recipe silently reports a circularity as lifted
metadata:
  type: project
---

Interface.lean's strong-multiplicity-one leaf carries a CIRCULARITY WARNING
whose recorded method is *"a cone walk over proof TERMS, run from a plain-import
(non-`module`) file — a `module` file exports no theorem bodies and reports a
false clean"*. Re-run exactly as prescribed on 2026-07-31 (release 33) it
returned `hits []` for all nine starting points **including the positive
control**, with cone sizes ~4900 against the ~69000 the note records.

**Why:** it is the IMPORTED file's module-ness that elides bodies, not the
importing file's. `Interface.lean` is itself `module` (line 134), so
`ConstantInfo.value?` is `none` for everything it exports and the walk stops at
the statement. `import all` does not help. The control lives inside the elided
file too, so the guard designed to catch this cannot.

**Why it matters:** the false answer is a POSITIVE one — "the consumers are
independent" — which licenses the Chebotarev + Brauer–Nesbitt route the leaf
forbids, i.e. proving a leaf out of theorems that rest on it.

**What works, in seconds and with no build:** build the call graph from SOURCE —
strip nested block comments, attribute tokens to the enclosing declaration by
walking back to the nearest header, BFS the reverse edges. Tokenise with
`isalnum() or c in "_'."`, never a unicode range
([[lean-identifier-regex-swallows-brackets]]). It over-approximates (signatures
count as uses), so confirm a hit by reading the line; a MISS is conclusive. It
sees one file, which is enough when the chain is in-file — check the endpoints.
Across files, append the `run_cmd` walk to the END of the declaring file, the
same rule [[flt-print-axioms-must-be-in-declaring-file]] states for
`#print axioms`.

**Why:** cheap checks that fail silently in the direction of "all clear" are the
worst kind, and this one is prescribed by name in a docstring that a successor is
told to read first.

**How to apply:** never accept a cone-walk clean result over an imported
`module` file; re-derive it from source, or from inside the declaring file.
