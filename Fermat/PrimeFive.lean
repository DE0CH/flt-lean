import Fermat.FreyCurve

/-!
# Fermat's Last Theorem for prime exponents `p ≥ 5`

This is the hard case of Fermat's Last Theorem, proved by Wiles and
Taylor–Wiles (1995) via the Frey–Serre–Ribet reduction to modularity of
semistable elliptic curves over `ℚ`.

Following the Frey-package normalization (`Fermat/FreyPackage.lean`), the
whole case reduces to `FreyPackage.false`: there is no Frey package. That
statement is the current root of the remaining dependency tree; its proof
goes through the Frey curve (`Fermat/FreyCurve.lean`) and the deep inputs
(Mazur irreducibility, modularity of semistable curves, Ribet level
lowering, and the absence of weight-2 level-2 cusp forms). See `PROGRESS.md`.
-/

/-- **There is no Frey package** (Mazur, Ribet, Wiles, Taylor–Wiles).
The `p`-torsion of the Frey curve of a Frey package would be an irreducible
(Mazur) 2-dimensional mod-`p` Galois representation which is modular of level
2 (Wiles' modularity plus Ribet's level lowering); but there are no nonzero
weight-2 cusp forms of level 2, a contradiction. -/
theorem FreyPackage.false (P : FreyPackage) : False := by
  sorry

/-- **Fermat's Last Theorem for prime exponents `p ≥ 5`** (Wiles,
Taylor–Wiles). If `p ≥ 5` is prime, then `a ^ p + b ^ p = c ^ p` has no
solutions in nonzero natural numbers. -/
theorem fermatLastTheoremFor_of_five_le (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    FermatLastTheoremFor p :=
  FreyPackage.fermatLastTheoremFor_p_ge_5 ⟨FreyPackage.false⟩ p h5 hp
