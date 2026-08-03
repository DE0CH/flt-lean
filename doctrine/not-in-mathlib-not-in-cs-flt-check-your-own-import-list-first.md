## "NOT IN MATHLIB, NOT IN `~/cs/FLT`" — CHECK YOUR OWN IMPORT LIST FIRST

(2026-07-31, `exists_idempotentLocalQuotient`.) That leaf's docstring prescribed a
four-step programme — `A` is `3`-adically complete, `A/3A` is artinian hence a product of
local rings, lift the primitive idempotents along the complete surjection, take `ε` to be
the lift of the sum of the ones `ū` kills — and called it "the half of the parent that can
be attacked without any of the complete-intersection theory", i.e. a genuine but bounded
piece of commutative algebra.

The whole programme was already proven in-tree, sorry-free, in a file **`ModThree.lean`
itself publicly imports** (line 435): `exists_isIdempotentElem_isLocalRing_quotient_of_moduleFinite`
in `Fermat/FLT/Mathlib/RingTheory/AdicCompletion/Finite.lean`, whose own docstring opens
by saying it supplies "what a survey of the mathlib pin found to be genuinely absent: the
decomposition of a module-finite algebra over a complete Noetherian local ring into local
factors". Given it, the leaf is ~30 lines: show `ker ū` is maximal (`A ⧸ ker ū` embeds in
the FINITE residue field `𝒪_E/𝔪`, so it is a finite domain, hence a field), feed it in,
and take `ε := 1 − e`.

The existing memory note is "missing machinery may be DOWNSTREAM" — in a file that imports
yours. This is the *easier* case and was missed anyway: it was UPSTREAM, in this module's
own import list, put there by an earlier owner for a different consumer. So the check
before writing any "expect to build it" in a docstring is mechanical:

    grep -n "public import" <your module> | ...        # then grep those files for the concept
    grep -rn "IsLocalRing\|IsIdempotentElem\|Henselian" Fermat/FLT/Mathlib/ | ...

`Fermat/FLT/Mathlib/**` in particular is where every agent's general-purpose commutative
algebra lands, it is small, and it is the first place to look — it exists precisely
because the pin was missing something.

