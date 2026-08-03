## A ROUTE'S "ELEMENTARY" STEP IS THE ONE NOBODY GREPS FOR — price EVERY step against the pin
(2026-08-02, `flt-lean-352`, on `artinMap_toPrincipalIdeal_of_isCyclic` in
`NumberField/ArtinSymbol.lean`.)  A mature leaf's ROUTE paragraph names a hard step and a
cheap one, and the cheap one is described in words that stop the reader searching: *"Artin's
own proof adjoins `ζ_m`, **where the Artin symbol is computable** (`Frob_𝔭 : ζ ↦ ζ ^ N𝔭`, so
reciprocity for `ℚ(ζ_m)/ℚ` is **the elementary congruence** …), and descends by the
translation theorem."*
Every absence claim in that docstring was re-checked and every one held — no class field
theory, no ray class groups, no Herbrand quotient, nothing in `~/cs/FLT`.  **The unchecked
clause was the reassuring one.**  `Frob_𝔭(ζ) = ζ ^ (N 𝔭)` is NOT in the pin:
`Mathlib/NumberTheory/Cyclotomic/` is five files and a grep of all of them for `Frob`,
`frobenius` and `IsArithFrobAt` returns **nothing**; `Gal.lean` gives only the ABSTRACT
`Gal(K(ζ_n)/K) ≃* (ZMod n)ˣ` (`autEquivPow`), with no arithmetic identification of the
Frobenius at a prime.  So the route's "elementary" first step is itself an unwritten leaf,
and the node is more expensive than its own docstring reads.
**The mechanism is structural, not careless.**  An author writes the absence audit for the
step they judged HARD, because that is the step they were deciding about.  The step they
called elementary is elementary *as mathematics*, and its formalisation status is a
completely independent question that nobody thought to ask — the adjective closes the
search.  This is the sibling of *inventory audits understate what exists*, in the opposite
direction: there an absence claim is wrongly negative, here a presence claim is merely
assumed.
**The check is mechanical: list the route's steps as a numbered chain and grep the pin for
EACH, including the ones the docstring calls elementary, classical, standard, computable,
immediate or bookkeeping.**  Those six adjectives are the search terms — a step carrying one
of them is exactly a step whose formalisation cost has not been measured.  Grep for the
OBJECT the step produces (here `Frob` in the cyclotomic directory), never for the theory's
name.  Cost: one grep per step; payoff: a route's true price, which is what every dispatch
downstream is sized against.
Corollary for whoever WRITES a route: an adjective is not a citation.  Say "in the pin as
`X`" or "NOT in the pin, checked `<date>`" for every step, or say nothing about its cost —
"elementary" is read downstream as "free", and it is the half of the estimate that never
gets re-derived.
