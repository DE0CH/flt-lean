## A RESTATED *PREDICATE* VOIDS THE AUDITS OF EVERY LEAF THAT MERELY USES IT

(2026-07-31, `flt-lean-337`.) This file already says a leaf restated a second time
inherits no audit. The same voiding happens one level DOWN, through a definition,
and it is much harder to see — because **the leaf's own statement never changes,
so nothing flags it.**

The instance. On 2026-07-30 `exists_traceGenerated_auxDeformationDatum` in
`Modularity/Patching.lean` gained a hypothesis `hktr` ("`k` is generated over
`ℤ_[p]` by `ρbar`'s residual Frobenius traces"), under a FALSITY AUDIT #4 that
proved it NECESSARY: the leaf's conclusion `IsTraceGeneratedDeformation` entailed
it, so without it the leaf was unprovable. The audit was correct, and it came with
a refuting instance (`ρbar₀/𝔽_p` base-changed to `𝔽_{p²}`) and a proven obstruction
theorem carrying the entailment.

On 2026-07-31 `IsTraceGeneratedDeformation` itself was restated — quantified over
subalgebras, with residual surjectivity moved from CONCLUSION to HYPOTHESIS. That
killed the entailment, and with it every word of audit #4: the hypothesis stopped
being necessary, and the obstruction theorem stopped being derivable and went RED.
Its own restating audit even said so, at point (ii) — "the derivation cannot be run
in reverse" — and still nobody connected that sentence to the leaf two thousand
lines below that had been built on the derivation.

So: **when you restate a definition, grep for every leaf whose audit ARGUES from
it, not just for every signature that mentions it.** And the restating audit's
companion claim here — "`hgen` is consumed by no proof body in the tree, so this
change is inert for the build and changes no signature" — was false at three sites.
It had been inferred from every *signature* merely forwarding `hgen`. The check
that would have caught it is one command: grep the BINDER NAME inside proof bodies,
not the predicate name in binder lists.

### And before threading a new hypothesis "up the chain", find where the chain ENDS

The prescription left for the red theorem was: delete it, and add `hktr` beside
`hgen` at the seven `Runiv`-consuming declarations that already forward `hgen`.
Every one of the seven is in `Patching.lean`, so the change looked self-contained.
It is not: the seventh, `injective_ringHom_of_isWeaklyUniversal`, is called twice
from `Modularity/Interface.lean`, where `hgen` is `obtain`ed from
`exists_weaklyUniversal_hardlyRamifiedDeformation` — which **cannot supply `hktr`**,
the base-change instance refuting it for a general coefficient field. Threading
would have exported an unprovable obligation across a file boundary and moved the
red downstream rather than removing it.

One command separates the two outcomes, and it costs nothing:

    grep -rn '<top name of the chain>' --include=*.lean Fermat/ | grep -v '<your file>'

Run it on the TOP of the chain before you touch the bottom. A hypothesis you cannot
discharge at the top is not a repair, however clean it looks at the leaf; the repair
that closes is usually the opposite move — **removing** the hypothesis the voided
audit added.

(Operational note from the same task: the doctrine's LEAN_PATH shim really does need
a single `cp -rs` farm. Putting an overlay directory FIRST in `LEAN_PATH` and the
release build second did **not** fall through — `lean` reported the overlay's path
as missing rather than finding the olean in the second entry. One farm dir, with
`cp --remove-destination` for the modules you rebuild.)


