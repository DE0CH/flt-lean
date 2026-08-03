## A DIMENSION-COUNT LEAF HAS TWO LAYERS THAT ARE NOT MATHEMATICS — CUT THEM OFF, AND LEAVE THE ESTIMATED BOX EXISTENTIAL
(2026-08-02, `flt-lean-116`, on `exists_stepanovIrrationalBranchLinearFormsField`
in `Modularity/Interface.lean`.) Schmidt's method — and every Stepanov-shaped node
in this tree — states its key step as
    ∃ (B : ℕ) (Φ : families →ₗ[K] (Fin B → K)),
      B < unknownCount ∧ ∀ a, shape a → Φ a = 0 → <the mathematics>
Three layers are bundled there and only one is mathematics: the PACKAGING (`Fin B`,
the linear map, coefficient extraction), the COUNT, and the actual theorem. Both of
the first two come out with an assembly that is ~120 lines and needs no input from
the residual leaf. Cut so the leaf produces the RAW OBJECTS the route builds — here
the reduced hyperderivatives `Θ ν : families →ₗ[K] K[X][Y][Y']` for `ν < M` — inside
a degree box, plus ONE arithmetic conjunct.
**THE PART THAT DECIDES WHETHER THE CUT IS SAFE: pin only what MONIC DIVISION
forces, and leave every ESTIMATE existential.** This node's own section note warns
that `stepanovEquationCount`'s constant `2d − 3` is TIGHT and that "pinning a
constant the route does not hit would manufacture a FALSE leaf". That warning is
about the `X`-degree, which is an estimate; it is NOT about `deg_{Y'} ≤ d − 2` and
`deg_Y ≤ d − 1`, which are what division by the two monic polynomials
`e₂ := (F(X,Y') − F(X,Y))/(Y' − Y)` and `F` LEAVES BEHIND. So:
* quantify the estimated bound: `∃ D : ℕ → ℕ`, with the single constraint
  `∑_{ν<M} (d−1)·d·(D ν + 1) < unknownCount`. Constraining the TOTAL rather than
  each `D ν` makes the leaf exactly as weak in the count as `B < unknownCount` was,
  so the cut cannot lose anything a prover could have used;
* keep the monic-division degrees pinned — they are the shape the count rests on;
* then PRE-PROVE the arithmetic for the box the route is expected to hit
  (`stepanov_schmidtBox_lt_unknownCount`, at `D ν = q/d − d + (2d−3)ν`), as a
  separate theorem the leaf's prover cites in one line. The obligation is discharged
  without being pinned, which is the whole point.
**THE ASSEMBLY, and the four places it fights back.** Index the box as
`(ν : Fin M) × (Fin (d−1) × Fin d × Fin (D ν + 1))` — a `Sigma` ONLY because the
`X`-degree depends on `ν`, the inner three factors being a plain product, which is
what makes `Fintype.card` a one-line `Fintype.card_sigma` + `Fin.sum_univ_eq_sum_range`.
Then:
* **do not compose typed `lcoeff`s.** `Polynomial.lcoeff R n : R[X] →ₗ[R] R` is
  linear over the COEFFICIENT ring, and the outer coefficient of `K[X][Y][Y']` is
  `K[X][Y]`-linear, not `K`-linear. Build `Φ` as a raw structure literal; both
  `map_add'` and `map_smul'` are `intro _ _; funext n; simp`;
* **to use `Φ a = 0` at a box index, use SURJECTIVITY, not the round-trip
  equation.** `rw [Equiv.apply_symm_apply]` fails because the pattern sits under an
  unreduced structure-literal application — the standing "printed pattern equals
  printed target" trap. Prove `∀ idx, <coeff at idx> = 0` by
  `obtain ⟨n, rfl⟩ := eqv.surjective idx; exact congrFun hΦ n`;
* **`Fin.mk` inside an anonymous constructor does not reduce for `omega`.** A bound
  `v < D ↑(⟨ν, hν⟩ : Fin M) + 1` is not something `omega` can see through; produce
  the bound as a `have` first and pass it, so the elaborator does the defeq;
* the ℕ-truncation points in the count are exactly two, and both need naming:
  `q/d − d + 1 ≤ q/d` needs `d ≤ q/d` (from `250d⁵ < q` via `Nat.le_div_iff_mul_le`),
  and `2·(d(d−1)/2) = d(d−1)` needs `d(d−1)` even, which is `Nat.even_mul_succ_self`
  after `(d−1)+1 = d`.
**ACCOUNTING: one leaf in, one leaf out; the direct-sorry count does not move, and
that must be said in the commit.** What changed is that the open statement mentions
no `Fin B`, no linear map into a finite tuple, and no dimension count. Judge it by
what is LEFT in the leaf.
### And the absence claim this cut re-priced: `Polynomial.hasseDeriv` IS the hyperderivative
Three docstrings in the same cluster say that over `𝔽_{p^f}` the jet route dies —
`stepanov_jet_dvd_core` needs `∀ j < M, (j! : K̄) ≠ 0`, i.e. `M < p`, while
`2d(M+8)² ≤ q` forces `M ≫ p` — and conclude that **"Schmidt's hyperderivative
calculus is genuinely required"**. The first clause is true; the second reads as a
theory that must be built, and the univariate half of it is in the pin:
    Mathlib/Algebra/Polynomial/HasseDeriv.lean
      hasseDeriv k : R[X] →ₗ[R] R[X]   -- over any CommRing, no factorials divided
      hasseDeriv_mul  (Leibniz, over `Finset.antidiagonal k`)
      hasseDeriv_comp, natDegree_hasseDeriv_le, factorial_smul_hasseDeriv
    Mathlib/Algebra/Polynomial/Taylor.lean
      taylor_coeff : (taylor r f).coeff n = (hasseDeriv n f).eval r
`factorial_smul_hasseDeriv : ⇑(k ! • hasseDeriv k) = derivative^[k]` is precisely
the diagnosis: `stepanovJet` is `k! • hasseDeriv k`, and it is DIVIDING BY `k!`
that needs `M < p`. What is genuinely absent is the calculus in the ring extension
`K[X][y]/(F)` — hyperdifferentiating a BRANCH — which is what §§7–9 is about.
**Say which of the two you mean**; "the hyperderivative calculus" names both, and a
cost estimate that names the wrong one sends the next agent to rebuild mathlib.
