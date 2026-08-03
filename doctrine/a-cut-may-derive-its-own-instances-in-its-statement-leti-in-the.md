## A CUT MAY DERIVE ITS OWN INSTANCES IN ITS **STATEMENT** — `letI` in the conclusion, not `[…]` in the binders
(Same task.)  A leaf cut out of a larger node often needs instances the parent
had derived internally — here `Fact ℓ.Prime` (for `Field (ZMod ℓ)`) and
`IsIntegral (special fibre)` (for `Scheme.functionField` and for
`functionFieldAlgebra`).  The reflex is to expose them as instance binders
`[Fact ℓ.Prime] [IsIntegral …]`, which type-checks and is wrong twice: the
consumer has to supply what the leaf's own hypotheses already imply, and a
reader cannot tell an instance binder that is DERIVABLE from one that is extra
strength.
A `letI` chain in the STATEMENT closes both holes, and it composes with a data
instance (`functionFieldAlgebra` is a `def`, deliberately not an `instance`):
    theorem foo … (hbase : IsReductionBase ℓ R toF) (hcurve : …) (hconn : …) … :
        letI : Fact ℓ.Prime := ⟨hbase.prime⟩
        letI : IsIntegral P := isIntegral_pullbackSpecial_of_isReductionBase hbase hcurve hconn
        letI := AlgebraicGeometry.functionFieldAlgebra (k := ZMod ℓ) strP
        ∃ f : P.functionField, Transcendental (ZMod ℓ) f ∧ …
Three things this buys, all checked here.  The leaf is **self-contained** — its
signature names only its own hypotheses.  The hypotheses used by the `letI`s
**stop being underscored**, which is this tree's own tell for "load-bearing", so
the binder list documents itself.  And at the call site the assembly's ordinary
`haveI`s **unify with the `letI`s for free** when the terms are written
identically: `Prop`-valued classes by proof irrelevance, and a DATA instance
because its `Prop` arguments are irrelevant, so `obtain … := foo hbase …` just
works and no transport appears.
The cost is one elaboration of each derivation inside the statement; measured
here that is invisible.  Prefer it to instance binders whenever the leaf can
derive them, and reserve `[…]` for the genuinely extra.
