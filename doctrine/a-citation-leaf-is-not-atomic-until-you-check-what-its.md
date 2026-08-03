## A CITATION LEAF IS NOT ATOMIC UNTIL YOU CHECK WHAT ITS NEIGHBOURS ALREADY PROVE
(2026-07-31, `exists_isFineGamma1Moduli`.) A leaf whose docstring is one citation
— "Katz–Mazur 4.7.1", "Deligne–Rapoport IV.2" — reads as irreducible, and the
reflex is to price the whole classical theorem. Ask instead **which parts of that
theorem the tree has already proven for a neighbouring leaf**, because a citation
is usually a conjunction and the sibling constructions have often discharged most
of it. Here the arithmetic half (4.7.0 + 2.7.4 + 8.1.1, every hypothesis on `N`
and `ℓ`) was PROVEN in `exists_gamma1AffineModel`, and the uniqueness half fell
out of a field the atlas structure already carried. What remained was one
base-generic, arithmetic-free leaf: the frontier count did not move, but the leaf
lost three hypotheses and became usable over `ℚ` as well.
Two rules came out of it, and both generalise past this file:
* **A `∀` over a structure is safe exactly when it constrains a field the
  structure PINS.** `X1.lean` has a refuted `∀ A : Gamma1Atlas` leaf and a sound
  one. The difference is not the quantifier: `A.M` (the rigidified scheme) varies
  with the auxiliary level and a `∀` about it must hold for all of them at once,
  while `(A.Y, A.classify)` is INITIAL among classifying cocones, so a statement
  about it has the same truth value at every atlas. Before writing or auditing a
  `∀ <structure>`, ask which field the conclusion mentions and whether the
  structure's own universal property determines it.
* **A uniqueness clause with no "over the base" clause is FALSE over any base
  with a nontrivial automorphism.** `IsFineGamma1Moduli.eq_of_isBaseChange`
  carried the note "uniqueness is a statement about `M` alone"; over
  `K = 𝔽_{ℓ²}` with `σ` the Frobenius, `m` and `Spec σ ≫ m` classify the same
  datum and differ. Rigidity pins the classifying morphism only *among morphisms
  over the base*. Such a notion is correct only where `Hom(T, S)` is a
  subsingleton — i.e. at `SpecQ` (`subsingleton_hom_specQ`) and `SpecF ℓ`
  (`subsingleton_hom_specF`), the two bases this development uses — so when you
  move one off its base, carry `∀ Z, Subsingleton (Z ⟶ S)` as a real hypothesis.
Consequence for the second rule that is easy to miss: a hypothesis can be
load-bearing **twice**. `ℓ.Prime` is cited for "`ZMod ℓ` is a field"; it is also
the reason the uniqueness clause is true at all, and that second role is
invisible until the statement is generalised.
**AND THE SAME COLLISION HAPPENS BETWEEN TWO *PROVEN* THEOREMS, WHERE NO LEAF IS FALSE AND NOTHING IS
EVEN OPEN** (2026-07-31, `Modularity/MoretBailly.lean`). The section above is about a LEAF going false.
This variant is worse to find, because every declaration involved stays true and green.
`exists_totallyReal_point_padicEmbedding_of_geometricallyIrreducible` needs a totally real `F` that is
BOTH of even degree AND admits `F →+* ℚ_[2]`. `Even (Module.finrank ℚ F)` was added to the supply chain
on 2026-07-29; the `ℚ_[2]`-embedding on 2026-07-30. Each is correct alone. Together they are
unsatisfiable *by that chain*, because the parity step enlarges `F` to `F(√d)` with `d` chosen by
`exists_padicSquare_nat_of_finset_primes` — a square at the Chebotarev primes `S` and carrying **no
condition at `2` whatever**, so it destroys exactly the embedding the other conjunct demands.
**Why no instrument could see it.** Both theorems were PROVEN and remained so; the build was green; the
sorry count did not move; no `sorry`, no error, no unreachable module. The broken thing is a *route
between two theorems*, and **no declaration in the tree states the composite property**, so there is
nothing for a falsity audit to attach to and nothing for a frontier scan to count. It was found only by
reading the two chains against each other from the consumer downwards.
So: **after adding a conjunct to a widely-consumed producer, walk its chain and ask what each later step
does to the conjuncts that were already there.** A step that CHOOSES something (a field enlargement, a
level, an auxiliary prime) is where conjuncts get destroyed, because it is free to choose badly.
**The repair shape is worth copying: strengthen the CHOICE, not the theory.** `d = (Q+1)² + Q` with
`Q = ∏_{p ∈ S} p` is an EXPLICIT witness with slack — `Q` may be any positive multiple. Taking
`Q = 8·∏_{p ∈ S} p` makes `d ≡ 1 (mod 8)`, hence a square in `ℚ_[2]`, while `p ∣ Q` for `p ∈ S` and the
non-square squeeze `(Q+1)² < d < (Q+2)²` (which needs only `0 < Q < 2Q+3`) are untouched. Total cost: one
factor of `8`, plus a `p = 2` Hensel companion that is the odd-prime proof with two lines changed
(`‖2‖ = 1` becomes `‖2‖ = 2⁻¹`, and `norm_int_lt_one_iff_dvd` becomes `norm_int_le_pow_iff_dvd` at
exponent `3`). **Before building theory to satisfy a new local condition, check whether the producing
witness is explicit and has slack.** Here it had, and the whole repair was ~40 lines.
Corollary for the conjunct itself: state it as an **implication in the conclusion**
(`Nonempty (F →+* ℚ_[2]) → Nonempty (F' →+* ℚ_[2])`), not as a new hypothesis. Every existing call site
then keeps compiling with one extra `-` in its `obtain`, and a call site that has no `p`-adic data to
offer is not forced to invent any.
