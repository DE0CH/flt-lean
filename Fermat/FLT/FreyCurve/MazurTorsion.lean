/-
MazurTorsion.lean — own work for the Fermat project (not vendored from the
FLT project).

Decomposition of `FreyPackage.mazur` (irreducibility of the mod-`p` Galois
representation on the `p`-torsion of the Frey curve) into two explicit
sorry nodes, following Serre's argument (Duke Math. J. 54 (1987), §4.1):

* `FreyPackage.exists_torsion_embedding_of_not_isIrreducible` (sorry node):
  **Serre's reducible-case analysis.** If the mod-`p` representation of the
  Frey curve `E` is not irreducible, then there is a Galois-stable line in
  `E[p]` (the `p`-torsion is `2`-dimensional over `𝔽_p`, so a proper nonzero
  invariant submodule is a line), i.e. a rational subgroup `C ⊆ E` of order
  `p`, giving an extension `0 → χ₁ → E[p] → χ₂ → 0` of characters with
  `χ₁ χ₂ = ω̄` (mod-`p` cyclotomic, by the Weil pairing). The Frey curve is
  semistable, so both characters are unramified away from `p` (unipotent
  inertia at multiplicative primes, triviality at good primes), and at `p`
  one of them is unramified (the supersingular case is excluded because
  inertia at `p` then acts irreducibly, contradicting reducibility). An
  everywhere-unramified character of `Gal(ℚ̄/ℚ)` is trivial (Minkowski: `ℚ`
  has no unramified extension). If `χ₁ = 1` then `E` has a rational point
  of order `p`; if `χ₂ = 1` then the quotient curve `E' = E/C` (a `ℚ`-rational
  quotient by a rational subgroup, Vélu) has one, namely the image of `E[p]`.
  Whichever curve carries the point of order `p` also carries full rational
  `2`-torsion: `E` visibly (`y² = x(x − aᵖ)(x + bᵖ)` has `(0,0)`, `(aᵖ,0)`,
  `(−bᵖ,0)`), and `E/C` because the quotient isogeny has odd degree `p`
  (so is injective on `E[2]`) and is defined over `ℚ`. Since `p` is odd,
  `(ℤ/2)² × ℤ/p ≅ ℤ/2 × ℤ/2p`, so SOME elliptic curve over `ℚ` has a
  subgroup of rational points isomorphic to `ℤ/2 × ℤ/2p`. The statement
  folds the quotient-curve construction (not yet available in mathlib) into
  an existential over Weierstrass models; a later layer must construct
  quotients by finite rational subgroups and split this node accordingly.

* `WeierstrassCurve.mazur_torsion_bound` (sorry node): **Mazur's torsion
  theorem, weak form.** No elliptic curve over `ℚ` has a subgroup of
  rational points isomorphic to `ℤ/2 × ℤ/2p` for a prime `p ≥ 5`. This
  follows from Mazur's classification of the possible torsion subgroups of
  `E(ℚ)` (the fifteen groups `ℤ/n` for `1 ≤ n ≤ 10` or `n = 12`, and
  `ℤ/2 × ℤ/2m` for `1 ≤ m ≤ 4`): a subgroup isomorphic to `ℤ/2 × ℤ/2p`
  is finite of order `4p ≥ 20 > 16`, while every group in the list has
  order at most `16`. A later layer must state the full classification
  faithfully and derive this weak form from it.

Given the two nodes, `FreyPackage.mazur` is immediate: if the representation
were reducible, the first node produces a curve whose rational points contain
`ℤ/2 × ℤ/2p`, which the second node forbids.
-/
module

public import Fermat.FLT.FreyCurve.Basic
public import Fermat.FLT.EllipticCurve.Torsion

@[expose] public section

open WeierstrassCurve WeierstrassCurve.Affine

/-- **Mazur's torsion theorem, weak form** (sorry node): the rational points
of an elliptic curve over `ℚ` contain no subgroup isomorphic to
`ℤ/2 × ℤ/2p` for a prime `p ≥ 5` — equivalently, no additive homomorphism
`ℤ/2 × ℤ/2p →+ E(ℚ)` is injective. A consequence of Mazur's classification
of torsion subgroups of elliptic curves over `ℚ` (fifteen groups, all of
order at most `16 < 4p`); a later layer must state that classification
faithfully and derive this from it. -/
theorem WeierstrassCurve.mazur_torsion_bound (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (φ : (ZMod 2 × ZMod (2 * p)) →+ (E⁄ℚ).Point) :
    ¬ Function.Injective φ :=
  sorry

/-- **Serre's reducible-case analysis for the Frey curve** (sorry node): if
the mod-`p` Galois representation on the `p`-torsion of the Frey curve is
not irreducible, then some elliptic curve over `ℚ` (the Frey curve itself or
its quotient by the resulting rational subgroup of order `p`) has a subgroup
of rational points isomorphic to `ℤ/2 × ℤ/2p` — full `2`-torsion plus a
point of order `p`. Serre, Duke 1987, §4.1: semistability forces one of the
two characters of the reducible representation to be everywhere unramified,
hence trivial (Minkowski), so `E` or `E/C` has a rational point of order
`p`; both curves have full rational `2`-torsion (visible Weierstrass form
resp. odd-degree rational isogeny). -/
theorem FreyPackage.exists_torsion_embedding_of_not_isIrreducible (P : FreyPackage)
    (h : ¬ (let E := P.freyCurve
            let p := P.p
            have : Fact p.Prime := ⟨P.pp⟩
            GaloisRep.IsIrreducible (E.galoisRep p P.hppos))) :
    ∃ (E' : WeierstrassCurve ℚ) (_ : E'.IsElliptic)
      (φ : (ZMod 2 × ZMod (2 * P.p)) →+ (E'⁄ℚ).Point), Function.Injective φ :=
  sorry
