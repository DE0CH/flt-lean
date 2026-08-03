## A LEAF CAN BE ATOMIC, AND SAYING SO IS WORTH AS MUCH AS A CUT
(2026-07-31, flt-lean-249, on `MazurCMForm.minpoly_eq_of_isCMJInvariant`.)
Task prompts in this fleet say "expect to DECOMPOSE rather than close", and the
standing tie-breaker is "prefer the cut that leaves the FEWEST OPEN leaves".
Both assume a cut exists. Sometimes none does, and the failure has a
recognisable SHAPE worth naming, because three plausible cuts fail against it
for one reason.
**When the target says "the orbit EXHAUSTS the set", nothing that says "the
orbit stays INSIDE the set" reduces it.** The CM main theorem here is
`Gal(ℚ̄/ℚ)` acting transitively on the CM `j`-invariants of one order. The
obvious companions —
* Galois STABILITY of the predicate (`IsCMJInvariant n x → IsCMJInvariant n (σ x)`),
* FINITENESS of the set,
* the DEGREE identity (`|orbit(x)| = deg_ℚ x`, so transitivity ⟺ `deg = |set|`),
— are each true, each independently useful, and each leaves the ENTIRE theorem
standing while adding a leaf. The first two are containment facts; the third is
circular, since `|set| = h(−4n)` is a SIBLING leaf's content. A cut is only a
cut if the residue is strictly smaller than the original; "peel off a true fact
the proof will also need" is not, and the leaf count makes it look like a loss
because it IS one.
**So write the ATOMICITY AUDIT into the leaf's docstring and commit that.** It
is cheap, it is checkable, and it is the only artefact that stops the next three
owners re-deriving it — the same role the FALSITY AUDITs already play. Name each
candidate cut and say which of "circular" / "containment, not exhaustion" /
"renaming" it is. Include the tempting steps that are FALSE, with the witness:
here, `ℚ(j(𝔟)) ⊆ ℚ(j(𝔞))` fails because `ℚ(j)` is NOT normal over `ℚ` (at
`D = −23`, `h = 3` and `Gal(H/ℚ) ≅ S₃`, so `ℚ(j)` is a non-normal cubic) even
though the ring class field `H = K(j)` is.
**And when the only move left IS a restatement, PROVE BOTH DIRECTIONS FIRST.**
A restatement that is accidentally STRONGER manufactures a harder — possibly
false — leaf while every frontier instrument reports an unchanged count. The
check costs one scratch module with the project predicate MOCKED as an opaque
`P : ℚ̄ → Prop`: state old ⇒ new and new ⇒ old and compile both. It took two
minutes here and it is what licenses the claim, written into the docstring, that
the trade is 1-for-1. (`minpoly ℚ y = minpoly ℚ x` for all CM `j`-invariants
⟺ some monic irreducible `p ∈ ℚ[X]` kills them all; `⇐` is
`minpoly.eq_of_irreducible_of_monic`, `⇒` takes `p = minpoly ℚ x₀`, or `p = X`
when the set is empty.)
Worth restating anyway when the new form is what the LITERATURE constructs: the
residual obligation became "build `H_{−4n}` and prove it irreducible", which is
Cox §11.1 verbatim, instead of a claim about `minpoly` — a derived notion no
step of the classical proof mentions.
