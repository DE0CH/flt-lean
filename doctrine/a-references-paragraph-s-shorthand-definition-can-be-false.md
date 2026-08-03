## A REFERENCES paragraph's shorthand definition can be FALSE — check it against a case you can compute
(2026-07-31, found while cutting `exists_eisensteinQuotientCert_of_jNeronDatum`.)
Every docstring in `MazurTorsion.lean` describing Mazur's Eisenstein quotient says
`I = (T_ℓ − ℓ − 1 : ℓ ∤ N)` and `J_e = J₀(N)/I·J₀(N)`. The first is right. **The
second is the ZERO abelian variety.** `𝕋 ⊗ ℚ ≅ ∏_f K_f` over the newforms of level
`N`; the component of `I` in the FIELD `K_f` vanishes only if `a_ℓ(f) = ℓ + 1` for
every `ℓ ∤ N`, which Deligne's bound `|a_ℓ| ≤ 2√ℓ < ℓ + 1` forbids for every cusp
form; so `I` has finite index `m` in `𝕋`, `m·1 ∈ I`, and `I·J ⊇ m·J = J` because
multiplication by `m ≠ 0` is surjective on an abelian variety. The object Mazur
means is `J₀(N)/℘·J₀(N)` with `℘ = ⋂_k I^k` — the `I`-adically-supported quotient,
isogenous to `∏ A_f` over the `f` CONGRUENT to the Eisenstein series.
Nobody wrote anything wrong: `J₀(N)/I J₀(N)` is standard shorthand in the
literature, and a citation is written for a reader who already knows the object.
But **a prover who formalises it literally gets `A = Spec ℚ`** — which here is
exactly the degenerate witness the sibling `IsCuspFormalImmersionCert` exists to
exclude, so the leaf would have been FALSE and its falsity would have looked like
a successful decomposition.
The check costs nothing and is the general rule: **before formalising an object
off a REFERENCES line, evaluate the proposed definition at one case you can
compute.** `N = 37`: `n = num((37−1)/12) = 3`, the Eisenstein prime is `(I, 3)`,
`J_e = A_{37b}` (rank `0`) while `37a` (rank `1`) is excluded. A definition that
returns `0`, or that returns all of `J₀(37)`, is refuted on the spot. This is the
same discipline as the file's non-vacuity witnesses, applied one level earlier —
to the DEFINITION rather than to the statement built from it.
