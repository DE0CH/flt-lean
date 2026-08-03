## A ℚ-CERTIFICATE CLEARS TO A **TORSION** STATEMENT OVER ℤ — AND THE MULTIPLIER IS BORN AFTER THE PARAMETER IT MUST DIVIDE
(2026-08-02, `flt-lean-119`, closing `exists_localizedSystemGens_identities_of_ratRetraction`
in `Modularity/MoretBailly.lean`.)  The leaf's route note prescribed the standard four
steps — write the values as fractions, push the equations down to numerators, clear
denominators into one integer `N`, choose an exponent past the nilpotencies — and its
last sentence was *"`N` is the product of the denominators … and over `ℤ` it is what
makes the identity true at all."*  Steps 1–2 are exactly right.  Step 3 is **circular**,
and the circularity is invisible until you write it:
* the conclusion is a membership `N * z ∈ span (gens … N)`, and the generating set
  **depends on `N`**;
* `z` is built out of the representatives, which are integral only once `N` is divisible
  by their denominators — so `N` is chosen first;
* the certificate for the membership is a ℚ-identity whose cofactors have their OWN
  denominators, producing a multiplier `M` only **after** `N` exists.  Nothing makes
  `M` divide a power of `N`.
**And `M | N^∞` is exactly what would be needed, because the leading `N` is decoration.**
The ideal contains `N · (rename some b) · X none − 1`, so `N` is already a UNIT modulo it
and `N * z ∈ span ↔ z ∈ span`.  What the factor was standing in for is the TORSION of
`MvPolynomial (Option (Fin k)) ℤ ⧸ span (gens … N)`: a `z` that dies over ℚ is only
torsion over ℤ, and killing it needs the torsion order inverted.  **It genuinely is not
automatic** — witness `k = 1`, `g = 2 X₀`, `b = 1`, `N = 1`, `z = X (some 0)`: the
quotient is `ℤ[X]/(2X)`, `z ↦ 0` over ℚ, and `z ∉ span {2 X (some 0), X none − 1}`.
**THE REPAIR IS A SUBSTITUTION, AND IT GENERALISES TO ANY "INVERT ONE MORE THING" LEAF.**
Rabinowitsch-style presentations are indexed by what they invert, so moving the index is a
change of variable: `X none ↦ M · X none` carries `gens … N₁` to `gens … (N₁ · M)`
generator by generator, and at the new level `M` **is** a unit (`M · (N₁ b y) ≡ 1`).  So
    M * z ∈ span (gens … N₁)   ⟹   subNoneMul M z ∈ span (gens … (N₁ * M))
with no multiplier left over.  The whole leaf then reads: do the construction at whatever
`N₁` clears the representatives, collect the certificate multiplier `M`, and transport.
**The one design decision this forces, and it is worth making on purpose: build the
`none` component of every tuple with an explicit `X none` factor.**  Transporting a
`bind₁ P₁ ·` along the substitution needs `M * P none = subNoneMul M (P₁ none)`, i.e. the
`none` component must be divisible by `M` after substitution — which is automatic exactly
when it was divisible by `X none` before.  Here that came free: the representative of
`Ψ((N·α)⁻¹)` is *(a representative of `Ψ(α⁻¹)`)* × `(rename some b · X none)`, because
`rename some b · X none` is precisely the integral expression for `1/N`.  **That is also
what makes integral representatives possible at all** — inverting `N · a` rather than `a`
puts `1/N` in the image of an integer polynomial — and the leaf's docstring says so, in a
paragraph headed WHY `N · a` AND NOT `a`, which is the most load-bearing sentence in it.
### The presentation lemma, and why to build the inverse instead of computing the kernel
`ker (aeval w) = span (gens)` and surjectivity of `aeval w` are both needed (the first to
turn "the value vanishes" into a polynomial membership, the second to get representatives
at all).  Do not chase either directly.  Build a two-sided inverse:
* `σ : Localization.Away x →ₐ[K] MvPolynomial (Option ι) K ⧸ J` by
  `IsLocalization.Away.liftAlgHom` of `Ideal.Quotient.liftₐ` of `rename some`, the unit
  witness being the `none` generator read as `θ x · ⟦N · X none⟧ = 1`;
* `σ ∘ aeval w = Ideal.Quotient.mk J` by `MvPolynomial.algHom_ext` — one generator each.
  At `X none` neither side is computable, and the move is
  `eq_of_mul_eq_one_of_mul_eq_one`: both `σ (w none)` and `⟦X none⟧` are right inverses of
  `N · θ x`.  **That lemma (already in this file) is the workhorse of the whole
  development — it is how you compare two inverses without ever writing an inverse**, and
  it is used four more times in the main assembly to identify `Ψ (w_A none)` and
  `Λ (w_B none)` with their representatives;
* `φ ∘ σ = id` on the localisation by `IsLocalization.ringHom_ext` (a map out of a
  localisation is pinned by its restriction along `algebraMap`).
`ker ⊆ J` then falls out of the first identity alone, and surjectivity out of the second.
No `IsLocalization.surj` is needed for the presentation; it is needed once, inside the
representative lemma, and there the fraction is immediately multiplied away.
### Four Lean traps, each one round trip
* **`ẑ` IS NOT A LEGAL LEAN IDENTIFIER AND `ĥ` IS.**  U+0125 (Latin Extended-A) is in
  Lean's identifier class; U+1E91 (Latin Extended **Additional**) is not.  The error is
  `expected token` pointing at the binder, which reads like a syntax error in the
  surrounding term.  Stick to ASCII plus subscripts for invented names.
* **`set L := SomeType` REWRITES THE TYPES OF EXISTING HYPOTHESES AND SHADOWS THEM.**
  Abbreviating a TYPE with `set` renamed `z`, `w` to `z✝`, `w✝` and introduced fresh
  copies at the abbreviated type, so every later `exact` failed on terms that print
  identically.  Abbreviate TERMS with `set` if you must; never types — write the type out.
* **A `hx : x = <unfolded>` argument passed as `rfl` UNIFIES `x` WITH THE UNFOLDED SIDE.**
  `canonicalTuple_none_spec f a N rfl wA …` came back stated about
  `Ideal.Quotient.mk (integralSystemIdeal f ℚ) (map a)` rather than about
  `integralSystemClass f ℚ a`, so every later `rw` missed.  Fix by giving the `have` an
  explicit TYPE ASCRIPTION in the form you want — the defeq check passes and the
  statement is then in your vocabulary, not the elaborator's.
* **When `rw [h]` fails inside a `have … := by rw [h, map_one]`, do it forwards:**
  `have h2 := congrArg Ψ h; rw [map_mul, map_mul, map_natCast, map_one] at h2; exact h2`.
  Rewriting a hypothesis you already hold cannot miss; rewriting a goal you wrote by hand
  can, and does, whenever the two spellings differ by a `def`.
### Accounting
`MoretBailly.lean` goes 20 → 19 direct sorries; the target and its consumer
`exists_pos_forall_prime_not_dvd_reduction_retraction_localizationAway_integralSystemModel`
both come back `[propext, Classical.choice, Quot.sound]` from `#print axioms`.  The 562
lines of presentation theory added above it are general — nothing in
`ker_aeval_eq_span_localizedSystemGens`, `exists_intRep_localizationAway`,
`exists_natCast_mul_mem_span_of_map_mem` or `upgrade_localizedSystemGens_identities`
mentions the Moret–Bailly setting — so a second consumer costs nothing.
