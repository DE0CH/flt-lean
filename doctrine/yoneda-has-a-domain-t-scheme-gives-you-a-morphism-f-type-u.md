## YONEDA HAS A DOMAIN: `∀ T : Scheme` GIVES YOU A MORPHISM, `∀ F : Type u, [Field F]` DOES NOT
(2026-08-02, `flt-lean-302`, leaf A2a1-ii of `Modularity/MoretBailly.lean`.) This file
already records the move that closes a whole class of leaves: **a functorial bundle
quantified over ALL TEST SCHEMES is a morphism — instantiate at the object itself and
feed it the identity** (`exists_end_of_relPointEndo`, `IsCMByRamifiedMaximalOrder.phi`,
`IsX0JNeronDatum`'s `spX`/`genX`). It is why several "this datum carries no map of
spaces, so the leaf is structurally underivable" verdicts were wrong.
**The converse matters just as much, and it is the thing to check FIRST because it
prices the leaf: a family quantified over FIELDS is NOT a morphism, and no amount of
naturality makes it one.** A fine-moduli property of the shape
    (∀ (F : Type u) [Field F] [Algebra ℚ F] (x : Spec F ⟶ X₀), … level structures at x)
  ∧ (∀ F, an object over F with level structures comes from an F-point of X₀)
pins `X₀` on points of FIELDS only. Yoneda needs all of `Scheme`; a bijection of
`F`-points for every field `F` does not determine a scheme — non-reduced test objects
are exactly what it cannot see — so `Aut_K (X₀ ⊗ K)` is unreachable from it. Concretely:
leaf A2a1-ii's `hmodel` hypothesis is field-indexed, so the transport of the
level-twisting cocycle `g` to `Aut_K (X₁ ⊗ K)` is **not** derivable from it, and the leaf
is a genuine citation (Taylor §4 / Rapoport §1) rather than the bookkeeping that its
"the group theory is already done and is handed in" docstring can be read as promising.
**The check is one line, and it is the quantifier's DOMAIN.** Read what the structure's
`∀` ranges over before pricing anything:
* `∀ (T : Scheme) (g : T ⟶ S), …` — evaluate at the object itself on `𝟙`; you have a
  morphism, and the leaf is usually bookkeeping;
* `∀ (F : Type u) [Field F], …` — you have points, and a leaf demanding a MORPHISM (an
  automorphism, an isogeny, a section, a group law) is real geometry.
**Corollary, and it is what makes a pinning recut defensible in every level-structure
moduli problem in this tree: over an ALGEBRAICALLY CLOSED base the Galois-equivariance
clause of a level structure is VACUOUS**, because it quantifies over
`Field.absoluteGaloisGroup F` and that is trivial at `F = K̄`. So `X ⊗ K̄` classifies the
same objects whatever representation normalises the level structure; every
`ρ`-normalised model is a `ℚ`-form of ONE `K̄`-scheme; and "the `ρ₀`-model is the twist of
the `ρ₁`-model on the SAME base space" is a legitimate pinning of the existential. It is
TRUE by the citation and NOT derivable from the field-indexed hypothesis — i.e. exactly
a judgement, to be written into the leaf's audit rather than assumed. Weigh it: pinning
buys the shape clauses and costs a prover who builds the model by an independent route
the comparison `Y₀ ⊗ K ≅ X₁ ⊗ K`.
**And when a recut is `1 → 1`, say so in the commit subject and say what got smaller.**
Here nine conjuncts of the open statement became four, the direct-sorry count did not
move, and a warning-set delta of `−1 +1` is otherwise indistinguishable from one closure
plus one unrelated disclosure.
