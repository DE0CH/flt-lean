## TWIST THE EMBEDDING, DON'T MOVE THE PRIME — a conjugated local element is a local element

(2026-07-31, `flt-lean-24`, proving `localInertia_le_fixingSubgroup_of_isUnramifiedAt_muSubfield`.)

Every local-to-global inertia leaf in this development quantifies over `σ * ñ * σ⁻¹`, a
CONJUGATE of the image of a local element `n ∈ localInertiaGroup ℓ`. The obvious reading — and
the one both leaf docstrings prescribed — is "build the embedding prime `Q₀ = ι⁻¹(𝔪)`, then move
it along the Galois orbit by `σ` and propagate by transitivity", which is what
`MinkowskiUnramified.lean`'s `inertia_eq_bot_of_exists_prime_over` does and what makes that file
long.

**The conjugation can be absorbed into the EMBEDDING instead.** With `ι : ℚ̄ → (ℚ_ℓ)ᵃˡᵍ` the
embedding underlying `Field.absoluteGaloisGroup.map`, set

    j := ι ∘ σ⁻¹.

`j` is another ring embedding `ℚ̄ → (ℚ_ℓ)ᵃˡᵍ`, and for `g = σ ñ σ⁻¹` one gets, from `lift_map`
alone and with no orbit argument at all,

    j (g x) = n (j x)     for every x.

So relative to `j`, the global `g` acts exactly as the local `n` acts relative to `ι`. The prime
`j⁻¹(𝔪)` is then directly `g`-inertial, and the conjugacy-propagation step does not appear.
Cost: three lines. The orbit route needs a transitivity theorem, `IsGaloisGroup` instances and
`exists_smul_eq_of_isGaloisGroup`.

**Second trick from the same proof: `by_cases` on the prime being `⊥` beats proving it proper.**
`Ideal.comap ψ 𝔪` is prime for free, but the inertia nodes want `Q ≠ ⊥`, and showing the
embedding prime is proper (`ℓ ∈ 𝔪`, i.e. `1/ℓ` is not integral over `ℤ_ℓ`) is where the
corresponding absolute proof spends most of its length. It is never needed: if `Q = ⊥` then
`τ • x - x ∈ ⊥` says `τ • x = x` outright, and `NumberField.eq_one_of_smul_eq_self` closes that
branch in two lines. Split on it rather than ruling it out.

**And the reason the whole thing was cheap: READ THE CALL SITE BEFORE PROVING ANYTHING.** Both
`muSubfield` inertia leaves were stated WITHOUT `IsGalois (muSubfield p) (extendScalars hEle)`,
and without it neither is reachable without first proving "a compositum of everywhere-unramified
extensions is everywhere-unramified" and passing to a normal closure. Both call sites already
held that instance — one `obtain`s it out of `exists_transport_unramifiedAbelian_to_muSubfield`,
the other proves it three lines earlier — so adding it to the statement changed no call site at
all. That is the same shape as `exists_artinDivisorNormIndex_le_ray_class` above: **the missing
hypothesis is usually already in the caller's hand, and a leaf's own docstring will not tell you
so.** Grep the call sites before deciding a leaf needs new theory.

Note `IsGalois ℚ L₀` is NOT similarly available and a prover should not reach for it: the caller
builds `L₀` as `IntermediateField.fixedField M'` for a subgroup `M'` that is only normal in
`Γ_{ℚ(μ_p)}` (it contains the commutators of `ker χ`), not in `Γℚ`. So the absolute node
`isUnramifiedAt_of_inertia_le_fixingSubgroup`, which needs `IsGalois ℚ L`, does not apply to `L₀`
directly — the sibling leaf's docstring suggestion to "reuse the absolute node at every `ℓ ≠ p`"
needs a normal closure first, and that is a real cost, not a bookkeeping step.

