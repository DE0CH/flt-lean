## A PROVEN HALF OF A BLOCKED LEAF BELONGS IN THE LEAF'S BINDERS, OR IT IS FLOATING
(2026-07-31, `flt-lean-384`, on `exists_intCube_jInvariant_heegnerPoint`.) The common shape at a
hard leaf: half of it is provable here and the other half needs a theory nobody has. The obvious
move — prove the provable half as a named lemma, cite it in the leaf's docstring, leave the leaf
`sorry` — **loses the work**. A sorried body contributes NO dependency edges, so the new lemma has
no consumer in the root cone; it is free-floating code, which this project forbids and the census
flags. The docstring citation is not a dependency.
The move that keeps it is to recut the leaf so that the proven half is a HYPOTHESIS of the open
half, and write the assembly:
    theorem provable_half : P := ⟨…⟩                 -- outright
    theorem open_half (h : P) … : Q := sorry         -- P is now in the binders
    theorem the_leaf … : R := by  … open_half provable_half …   -- consumes BOTH
Now the leaf's own proof term mentions `provable_half`, so it is in the cone; the count is
unchanged `1 → 1`; and the next agent finds the hard half stated with its input already in hand.
Here `P` was "the multiplier `γ₂ ∘ γ = χ(γ)·γ₂` is a `MonoidHom` into `μ₃`" (proven from `η`'s and
`E₄`'s `S`- and `T`-transformations plus `SpecialLinearGroup.SL2Z_generators`, ~70 lines) and `Q`
was Weber's `γ₂(τ₀) ∈ ℚ`, which still needs Shimura reciprocity.
**Pick the STRONGEST `P` the assembly can consume, not the first one that compiles.** The first
cut here took `P` in per-`γ` existential form and queued the `MonoidHom` upgrade as future work;
the upgrade was twenty lines (multiplicativity IS uniqueness of the constant, and uniqueness needs
only one point where `γ₂ ≠ 0`), and the weak form does not express the thing the next agent
actually needs — that `ker χ` is a subgroup of index dividing `3`. A hypothesis you are about to
hand to someone else is worth one extra pass.
Two constraints on doing this honestly, both from sections above. The recut RENAMES the open leaf
while the old name survives as a PROVEN theorem, so it must be announced in `queue` and
`to_merger` — nothing downstream can infer a rename from a warning-set delta. And every clause you
put in the hypothesis must be one the assembly actually consumes: an extra "might be useful" clause
is unprovable-obligation-shaped and, if it is ever discharged separately, floating again.
**Corollary for the sceptical reading of this move.** A hypothesis-shaped remainder is logically
equivalent to the original leaf, so the count does not move and nothing was "closed". That is the
point: the deliverable is a proven theorem that could not otherwise be kept, plus a better-posed
residue. Judge it by whether the hypothesis is real mathematics, not by the count.
