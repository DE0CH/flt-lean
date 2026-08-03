## READING A MERGE SPLICE: three signatures, and one message that does not mean what it says
Same day, same file. Textual merges in this development produce a recognisable damage
pattern, and one of its symptoms is systematically misread.
* **`error: unexpected token ':='; expected command`** — two declarations spliced: one's
  signature followed by another's `:= by` and body. Seen as
  `… = (taylorWilesAug p q).map diamond :=` immediately followed by
  `Function.Surjective pres := by`.
* **A stray line inside a proof body** (`      (∀ i, n ≤ e i) ∧` between two `obtain`s) —
  a leftover of a conclusion that was edited on one side.
* **A lost `/--`** — the deadliest, because it reports NOTHING at the damage site. The
  prose of the next docstring is absorbed into the previous declaration's *value*, and
  with `autoImplicit` on, every word becomes an auto-bound implicit and the declaration
  elaborates to junk. `abbrev taylorWilesCoordModel … := Fin d → … ⧸ taylorWilesLevelIdeal p e`
  silently swallowed `see the reduction audit recorded there.` and the six lines after it.
**And the message that misleads:** `invalid use of explicit universe parameters, 'X' is a
local variable`. This does NOT mean `X` is shadowed. It means **`X` IS NOT IN THE
ENVIRONMENT AT ALL** — autoImplicit bound the unknown name as a local, and `X.{u, v}` on
a local is then illegal. So the message is a report about a declaration that failed or
was swallowed somewhere *above*, not about the line it points at. Four such messages
(`IsCohenCoefficients`) plus a dozen `Function expected at` (`taylorWilesCoordModel`) all
traced back to that one missing `/--` 8000 lines earlier.
Corollary for triage order: fix the FIRST parse error and the FIRST swallowed declaration
before believing any later diagnostic. In this instance 4 root defects accounted for
about 40 of the 52 reported errors.
