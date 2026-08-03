## A CHAIN PARAMETERISED BY A BUNDLED DATUM IS USUALLY LEVEL-GENERIC — MEASURE THE PROJECTIONS BEFORE PRICING A TRANSCRIPTION
(2026-08-01, `flt-lean-12`, `HardlyRamified/HilbertModularity.lean`.) This development
states long proof chains over bundled data — `HilbertDeformationDatum`,
`HilbertAuxDeformationDatum`, `Gamma0Datum`, `IsX0JNeronDatum` — and the two levels of a
bundle differ in ONE field. A chain written against the bottom-level bundle is then
unusable at the raised level, and the reflex price is "transcribe it", which for the
Carayol/Rouquier–Nyssen chain here was **six theorems and ~800 lines**. Its own docstrings
say so, and the raised-level leaf had been sitting behind that estimate.
**The estimate is checkable in about a minute, and it was wrong by two orders of
magnitude.** Strip comments, take each theorem's body, and regex out the set of `𝒟.foo`
projections it actually uses:
    projs = sorted(set(re.findall(r'𝒟\.(\w+)', body)))     # per theorem, comment-stripped
The answer here: all six use only `R`, `isAdic`, `isAdicComplete`, `ρ`, `π`,
`π_surjective`, `resid` — **and exactly ONE LINE in one of them reads the level-specific
field**, `𝒟.isHilbertHardlyRamified.det`. `IsHilbertRaisedLevelHardlyRamified.det` is that
clause character for character. So the chain was never bottom-level mathematics; only its
binder was. Replacing the datum binder by the ingredient list took **6 signatures and 7
call sites**, every one of which passed `𝒟` in the same position.
**Do it as an INGREDIENT LIST, not as a new shared structure.** A `HilbertFramedDatum`
plus two coercions is the tidier design and it puts `𝒟.toFramed.R` where `𝒟.R` used to be
— defeq by structure eta, and NOT syntactically equal, so every `rw` in every consumer
becomes a coin flip (the standing "printed pattern equals printed target" trap). Passing
`𝒟.ρ 𝒟.isHilbertHardlyRamified.det 𝒟.π 𝒟.π_surjective 𝒟.resid 𝒟.isAdic 𝒟.isAdicComplete`
keeps the conclusion literally about `𝒟.ρ` and `𝒟.R`, so the change is **strictly additive
at every call site** and cannot regress a consumer.
Three mechanical notes, each of which cost one 3-minute round:
* **A parameter that occurs ONLY inside an instance binder cannot be inferred.** The
  extracted `rank_eq_two_of_framedResid` carried `{ℓ : ℕ}` and `[Algebra ℤ_[ℓ] R]`, and
  every call died with `typeclass instance problem is stuck: Algebra ℤ_[?m] R`. `ℓ` is not
  determined by `ρ`, `π`, `hresid`. Either make it explicit or — better — check whether
  the proof needs it at all; this one did not, and dropping both the parameter and the
  instance was the fix.
* **Underscore-prefix the binders a given theorem does not consume**, per theorem, not
  uniformly. A uniform ingredient list is nicer at call sites and produces
  `unusedVariables` warnings on the theorems near the top of the chain; `_hpi`/`_hadic`/
  `_hcompl` are still explicit and still passed positionally, so call sites stay uniform
  while the non-use stays mechanically visible.
* **`open scoped TensorProduct in` is per-declaration and goes ABOVE the docstring.** A new
  leaf whose SIGNATURE mentions `⊗[…]`, or whose PROOF mentions `⊗ₜ`, needs its own copy;
  without it the error is a bare `expected token` at the `⊗` column, which reads as a typo.
**And the verification that makes such a refactor safe is the sorry-set diff BY NAME**, not
by count and not by line: the edit shifted every later line by 103, so line-keyed
comparison is useless. Extract each `declaration uses 'sorry'` warning's line, attribute it
to the enclosing declaration, and compare the two NAME sets — `IDENTICAL` is the receipt
that a generalisation proved and broke nothing.
Corollary about what a "LEAF" in a docstring is worth: this leaf's header called its
base-level twin `exists_framedGaloisRep_descent_hilbertTraceSubring_of_isWeaklyUniversal`
"the base-level LEAF". **That theorem is PROVEN**, and has been for days; what is open at
base level is one CLAUSE beneath it. The stale word is what made the raised-level node look
like an open descent rather than a proven descent over open clauses, and it is the single
sentence that decides whether a successor transcribes a proof or reuses one. Same family as
the standing rule that a `(sorry leaf)` header outlives the leaf — here in the more
dangerous direction, since it invents work rather than hiding it.
