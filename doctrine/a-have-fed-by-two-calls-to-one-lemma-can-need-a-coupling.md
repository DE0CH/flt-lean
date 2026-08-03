## A `have` FED BY TWO CALLS TO ONE LEMMA CAN NEED A COUPLING NEITHER CALL EXPORTS

(2026-07-31, flt-lean-201.) `hbase`, the last sorried `have` inside
`exists_artinNormSubgroups_ramified_ray_class`, was **not provable where it stood** — and
the reason is invisible to every check this file already prescribes.

Its enclosing proof applies ONE existential lemma
(`exists_artinAuxiliaryNumberField_ray_class`, Artin's Lemma) TWICE, at `v` and at `v₀`,
obtaining two auxiliary fields `E₁`, `E₂`. `hbase` then needs a fact about the
**compositum** — `M ∩ E₁E₂ = F`, equivalently that `χ` is surjective on `H₁ ⊓ H₂`. The
only coupling between the two calls was `hm₂cop`, coprimality of the two moduli, and
coprimality does not imply it:

    F = ℚ, M = ℚ(√-15), mm = (15), m₁ = 5, E₁ = ℚ(√-3), m₂ = 3, E₂ = ℚ(√5),
    v = 7, v₀ = 11

satisfies every clause of the lemma at BOTH calls — `M ∩ E_i = ℚ`, `M ⊆ E_i(ζ_{m_i})`,
`M ∩ ℚ(ζ_{m_i}) = ℚ`, `7` splits in `ℚ(√-3)`, `11` splits in `ℚ(√5)`, `5 ∤ 3` — while
`E₁E₂ = ℚ(√-3,√5) ⊇ M`. Then `χ(H₁ ⊓ H₂) = {1}` but `χ(globalFrob 11) = -1`, and no
witness exists. **This is the DEFAULT output of Artin's construction, not a pathology**:
`E_i` is the fixed field of a cyclic subgroup of `Gal(M(ζ_{m_i})/F)` projecting onto
`Gal(M/F)`, and `ℚ(√-3)`, `ℚ(√5)` are exactly such fixed fields.

**Why nothing catches it.** The two calls are individually correct; the lemma is
individually true; the `have`'s hypothesis list is individually satisfiable; a falsity
audit of the LEMMA passes. The defect lives in the *space between two applications*, which
no single statement mentions. It is the multi-call analogue of "TWO INDIVIDUALLY-CORRECT
REPAIRS CAN BE FATAL TOGETHER" above.

**The check to run**, whenever a proof applies one `∃`-lemma more than once and later
relates the outputs: *write down what the later step needs about the PAIR, and find the
clause that supplies it.* If no clause mentions both outputs, you have found a defect, not
a hard step. Reading the `have`'s binders will not reveal it — flt-lean-266 checked those
binders carefully in 2026-07-28, correctly found them insufficient, correctly recorded
"do not hoist with its own argument list", and still missed this, because the missing fact
was not missing from the *list*, it was missing from the *scope*.

**The repair shape**: make the second call RELATIVE to the first — a new leaf
`exists_relArtinAuxiliaryNumberField_ray_class` taking the first subgroup `H₀` as input and
exporting `ker χ · (H ⊓ H₀) = Γ F`. In Artin's construction this costs one extra condition
on the auxiliary primes (require them unramified in `M E₀`), i.e. it is a change to the
CHOICE OF THE MODULUS, which is where such conditions always belong.

Two smaller things fell out and are worth keeping:

* **A prime beats a compositum.** The route note prescribed `β = N_{E/F} B_E` over
  `E = E₁E₂`, needing the compositum as a field, the tower identity
  `N_{E/F} = 𝔑_i ∘ N_{E/E_i}`, and Chebotarev at `E`. What actually works is ONE prime `p`
  of the base splitting completely in both `E_i`, obtained from Chebotarev at `F` in the
  coset `σ₀ · (H₁ ⊓ H₂ ⊓ V)`. The compositum survives only as the Galois-theoretic clause.
  Before formalising a construction "over the compositum", ask whether a prime of the base
  with the same splitting behaviour does the job.
* **Chebotarev gives a CONJUGATE.** `exists_frobenius_conj_mem_coset` puts
  `g · globalFrob p · g⁻¹` in the coset, never `globalFrob p`; consumers that ask for the
  literal `globalFrob p ∈ H` therefore need `H` NORMAL. It always is in these
  constructions (`H` is the preimage of a subgroup of a commutative quotient) — but export
  the clause, do not assume it. Threading it down from
  `exists_subgroup_of_independent_ray_class` cost four lines.

