## A RECORDED ROUTE CAN FAIL ON *UNIVERSES*, AND NO AUDIT IN THIS FILE LOOKS THERE

(2026-07-31, `flt-lean-244`.) Every "route audit" discipline above reasons about
mathematics, instances, definitional equality and staleness. A route can be
mathematically correct, instance-correct, current — and still name a term that does
not elaborate, because the two objects live in **independent universes**. That failure
is invisible to a reader, invisible to `git log`, invisible to the frontier scans, and
it does not look like a universe problem when it bites: `@h k` simply reports a type
mismatch between `Type uK` and `Type uR`.

Two instances in one node, both recorded as settled by careful previous owners:

- `isAuxWeaklyUniversalOnFrames_of_isStrictlyUniversalOnFramesFor` prescribed
  "recover `ρbar`'s determinant by instantiating the levelwise pushforward clause at
  `A := k`". That clause quantifies over `A : Type uR`; `k : Type uK`. **It is a hard
  universe error.** The repair took the residue quotient `R ⧸ ker πuniv` instead —
  same mathematics, and it lives in `Type uR` *by construction*, which is the general
  shape of the escape: when you need an object in the coefficient universe, look for a
  QUOTIENT OF SOMETHING ALREADY THERE rather than for the thing itself.
- Its sibling `exists_levelIdealSystem_aux_of_clauses` asks for `P : Type uR`, and the
  base-level construction it is told to transcribe verbatim builds `P` out of one
  polynomial generator per element of `k`, hence in `Type uK`. **`ULift` does not
  repair this** — `ULift.{uR} X` for `X : Type uK` lands in `Type (max uK uR)`, not in
  `Type uR`. The escape again came from a hypothesis that already carried a `Type uR`
  object surjecting onto `k` (a bundled deformation datum's ring), so `k` has a small
  model in the right universe and the generators can be re-indexed by it.

Two things follow, and the second is the useful one.

**A universe generalization that "fixes the universes" may fix only ONE axis.**
`flt-lean-39` freed the COEFFICIENT universe of this chain and its audit says so
accurately; the RESIDUAL-FIELD universe was never mentioned, and that is the axis that
actually blocked the transcription. When a note says universes were dealt with, ask
*which* universe.

**Check universes FIRST when a route is handed to you, before reading the
mathematics.** It costs one `#check`-shaped elaboration of the route's key application
and it is the cheapest disproof available: a route that fails here fails before any of
its mathematics matters, and — unlike a stale claim — no amount of merging `main`,
rebuilding `.lake` or re-reading the literature will ever make it true.

