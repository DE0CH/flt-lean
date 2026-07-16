/-
TorsionCard.lean — own work for the Fermat project (not vendored from the
FLT project).

Decomposition of `WeierstrassCurve.n_torsion_card`
(`#E(k̄)[n] = n²` for `(n : k) ≠ 0`, `Torsion.lean`) into two faithful
arithmetic nodes:

* `TorsionCard.smul_surjective` (sorry node): **divisibility of the
  points group** — over a separably closed field, multiplication by
  `n` with `(n : k) ≠ 0` is surjective on the points of an elliptic
  curve. (The multiplication-by-`n` map is a finite separable isogeny of
  degree `n²`; over a separably closed field a separable isogeny is
  surjective on points.)

* `TorsionCard.prime_torsion_card` (sorry node): **the prime-level
  count** — for a prime `p` with `(p : k) ≠ 0`, the `p`-torsion of an
  elliptic curve over a separably closed field has exactly `p²`
  elements. (The kernel of the degree-`p²` separable isogeny `[p]` has
  as many points as the degree; concretely: the division polynomial
  `ΨSq p` is separable of the appropriate degree and each root carries
  the right number of ordinates.)

Derivation plan for `n_torsion_card` (a later layer): for a prime power
`p^(k+1)`, multiplication by `p` restricts to a surjection
`E[p^(k+1)] → E[p^k]` (surjectivity from the first node applied inside
the torsion tower) with kernel `E[p]`, so
`#E[p^(k+1)] = #E[p] ⬝ #E[p^k] = p² ⬝ p^(2k)` by induction; for general
`n = ∏ pᵢ^{kᵢ}` the torsion splits by CRT
(`TorsionCounting.torsionBy` machinery, already in the tree), giving
`#E[n] = ∏ pᵢ^(2kᵢ) = n²`.
-/
module

public import Fermat.FLT.EllipticCurve.Torsion

@[expose] public section

namespace TorsionCard

open WeierstrassCurve WeierstrassCurve.Affine

universe u

variable {k : Type u} [Field k] (E : WeierstrassCurve k) [E.IsElliptic]
  [DecidableEq k]

set_option warn.sorry false in
/-- **Divisibility of the points group** (sorry node): over a separably
closed field, multiplication by `n` with `(n : k) ≠ 0` is surjective on
the points of an elliptic curve — the multiplication-by-`n` isogeny is
finite and separable, hence surjective on points of a separably closed
field. -/
theorem smul_surjective [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Function.Surjective (fun P : (E⁄k).Point => (n : ℤ) • P) :=
  sorry

set_option warn.sorry false in
/-- **The prime-level count** (sorry node): for a prime `p` with
`(p : k) ≠ 0`, the `p`-torsion of an elliptic curve over a separably
closed field has exactly `p²` elements — the kernel of the separable
degree-`p²` isogeny `[p]` has as many points as its degree. -/
theorem prime_torsion_card [IsSepClosed k] {p : ℕ} (hp : p.Prime)
    (hchar : (p : k) ≠ 0) :
    Nat.card (E.nTorsion p) = p ^ 2 :=
  sorry

end TorsionCard
