## CUT SO THE TWO HALVES SHARE NO DATUM — AND A NONDEGENERACY CLAUSE NEVER NEEDS THE ISOMORPHISM
(Same task, and it is what made the two residues separately ownable.) A leaf of the shape
    ∃ inv : H ≃ₗ[k] k, ∀ …, (∀ x ≠ 0, ∃ y, inv (P x y) ≠ 0) ∧ (∀ y ≠ 0, ∃ x, inv (P x y) ≠ 0)
invites a decomposition in which BOTH halves mention `inv`, because the statement does:
half one produces it, half two asserts nondegeneracy *of the composite*. That cut is
legal and it is bad — the two leaves are then coupled through a datum, so they cannot go
to different owners, and the second one cannot be stated in the vocabulary of the
literature (which never mentions a choice of invariant map).
**They need not be coupled, because nondegeneracy is invariant under composing with any
linear isomorphism**: `inv z ≠ 0 ↔ z ≠ 0`, `inv` being injective. So state the second
half about the RAW pairing, with no `inv` anywhere; the assembly is then `obtain` the
isomorphism from half one and transfer both directions by `LinearEquiv.map_eq_zero_iff`.
Here that took the residues from "the invariant map, and duality composed with it" to
"the invariant map" (NSW VII.5) and "Tate duality" (NSW VII.2) — two citations, disjoint.
**The general test: for each clause of the conclusion, ask which of the existential's
data it actually CONSTRAINS.** A clause that is invariant under the symmetries of that
datum (scaling, composition with an automorphism) does not constrain it, and should be
stated without it. This is the dual of the standing rule that a `∀`-over-a-structure leaf
must not distinguish things the structure fails to pin: there the danger is asserting too
much about an unpinned datum, here it is carrying a datum a clause never reads.
Two riders from the same cut, both about what the decomposition should NOT be:
* **A cut that lands in a DIFFERENT COEFFICIENT RING costs two extra leaves.** The build
  order proposed `H²(ℚ_v, μ_ℓ) ≅ ℤ/ℓ` plus a base change to `k`. `μ_ℓ` is a `ZMod ℓ`-module
  and the file has no such object, and the base change needs a flat-base-change comparison
  for CONTINUOUS cohomology which is not in the pin — so `1 → 3`, two of them manufactured
  by the split. Stated directly over `k`, which is what the consumer asks for anyway, it is
  one leaf in vocabulary the file already has.
* **State the duality over an ABSTRACT PERFECT PAIRING, not over `Hom(M, μ)`.** The
  classical statement pairs `M` against its dual, and transcribing that forces the consumer
  to transport the cup product along `ad⁰(1) ≅ Hom(ad⁰, k(1))` — i.e. to prove NATURALITY
  OF THE CUP PRODUCT IN THE COEFFICIENT PAIRING, which nobody has written. Taking an
  arbitrary intertwining pairing that is nondegenerate on both sides makes the consumer's
  obligation exactly the already-proven `adZeroTraceForm_nondegenerate`. The two forms are
  equivalent whenever the target is one-dimensional (each nondegeneracy is an injection into
  a dual, and the two injections force equal dimensions), so nothing is given up.
