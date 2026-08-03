## CONSTRUCT THE ELEMENT; DO NOT PROVE THE GROUP IS BIG

(2026-07-31, `flt-lean-15`, closing `exists_galoisFixing_cyclotomic_not_isSquare` — the
leaf the section above says was correctly cut. It is the sequel to that section: the
survey named the right PROPOSITION, and was still wrong about the ROUTE.)

The leaf asks for `σ ∈ G_ℚ` fixing `v` (`v² = −1` or `v² + v + 1 = 0`) with `χ̄_cyc(σ)` a
non-square mod `p ≥ 5`. Its docstring surveyed two routes and recommended the second:

1. Frobenius + `cyclotomicCharacterModL_globalFrob` — rejected, needs **Dirichlet on
   primes in arithmetic progressions**, which is genuinely not in this tree;
2. a **degree computation**: `K ⊄ ℚ(μ_p)` because `φ(4p) = 2(p−1) ≠ p−1 = φ(p)`, hence
   `K ∩ ℚ(μ_p) = ℚ`, hence `χ̄_cyc` is onto on `G_K` — via `IsCyclotomicExtension.finrank`,
   `Nat.totient_mul` and "the bookkeeping of subfields of `AlgebraicClosure ℚ`".

The proof that closed it does neither. It **never mentions `K`, never compares two
degrees, and never intersects two subfields.** It builds `σ` directly: work at the
COMPOSITE level `m = n·p` (`n = 4` or `3`), take `c` with `c ≡ 1 mod n` and `c ≡ a mod p`
for `a` a non-square (`Nat.chineseRemainder`, legitimate exactly because `p ≥ 5` makes
`gcd(n,p) = 1`), and realise `c` as an automorphism. It fixes `v` because `v ∈ μ_n` and
`c ≡ 1 mod n`; it acts on `μ_p` by `a` because `c ≡ a mod p`. **90 lines, three mathlib
citations, no number theory of `K` at all.**

**The general shape, and it is worth reaching for by default.** Route 2 proves *the image
of a character is large*, then extracts an element from a large group. Constructing the
element skips the middle step — and the middle step is where all the cost was, because
"the image is large" is a statement about a lattice of subfields while "here is the
element" is a statement about one automorphism. Ask which one you actually need. A leaf
of the form `∃ σ, P σ` almost never needs a surjectivity theorem.

**Why it is specifically cheap here: irreducibility of `Φ_m` over `ℚ` is ONE theorem
covering every `m` at once.** `Polynomial.cyclotomic.irreducible_rat` feeds
`IsCyclotomicExtension.autEquivPow` (`Gal(ℚ(μ_m)/ℚ) ≃ (ℤ/m)ˣ`) at level `n·p`, and
`AlgEquiv.liftNormal` extends to `ℚ̄`. The fact `K ∩ ℚ(μ_p) = ℚ` that route 2 would have
established by a totient count is *carried for free* by that one citation. So when a
survey proposes to prove a compositum is as large as possible, check whether a single
irreducibility/degree theorem at the composite modulus already says it.

Reusable pieces this left in `X0.lean`, both stated over an arbitrary modulus and worth
knowing about before re-deriving them: `exists_algEquiv_pow_of_coprime` (surjectivity of
the mod-`m` cyclotomic character of `ℚ`, phrased as "some `σ` raises every `m`-th root of
unity to the `c`") and `exists_galoisFixing_cyclotomicCharacterModL_eq` (the CRT step).

### The `Algebra ℚ ℚ̄` diamond bites every proof that touches `AlgebraicClosure ℚ`

Already documented in `QuarticTwist.lean` and `ComplexConjugation.lean`, repeated here
because it cost an iteration and the symptom is unhelpful: **`Algebra.IsAlgebraic ℚ ℚ̄`
and `IsAlgClosure ℚ ℚ̄` do not synthesise anywhere in this tree**, because search finds
`DivisionRing.toRatAlgebra` while mathlib's instances are stated for
`AlgebraicClosure.instAlgebra`. `IsAlgClosed ℚ̄` *does* synthesise, so the failure looks
arbitrary. Supply them by hand — the `Patching.lean` idiom, which is four lines and works:

    haveI halgQ : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
    haveI hacQ  : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, halgQ⟩
    haveI hnormQ : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ _
    haveI hintQ : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) := halgQ.isIntegral

Do not try to fix it by re-declaring the mathlib instance in your file; the diamond is in
the `Algebra` instance itself, so no re-export reaches it.

And the coercion trap two sections above fired **twice more** in this proof, both times
in its documented shape — printed pattern equal to printed target, `rw` unable to cross:
once on `absoluteGaloisGroup ℚ`'s type ascription (cured by `Eq.trans`), once on
`autEquivPow`'s forward map versus `(zeta_spec …).autToPow`, which are the same function
behind a `MonoidHom`/`MulEquiv` coercion (cured by *stating* the equation and closing it
with `exact`, letting the defeq check do the work). Treat that pair as the standard cure.

