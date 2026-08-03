## "EXPECT TO DEFINE X" IS A CLAIM ABOUT ONE ROUTE — AND THE FREE TEXTBOOK MAY NOT BE THE ONE EVERY DOCSTRING CITES
(2026-08-01, `flt-lean-174`, `ModThree.lean`'s Demazure–Gabriel leaf.) That leaf's docstring
ended with a "WHAT IS STILL MISSING AND MUST BE WRITTEN" paragraph whose factual half was TRUE
and re-checked — mathlib has `HopfAlgebra`, `Ideal.IsHopfIdeal` and a quotient Hopf structure, and
**no Hopf subalgebra, no Frobenius kernel, no faithful-flatness theorem** — and whose inference
was wrong twice: *"the filtration by Frobenius kernels — the only known route — has no starting
point in the pin.  A successor should expect to define it."*
**No Frobenius-kernel filtration is defined anywhere in the actual proof.**  Milne runs the
induction on `dim_k A` through the single Hopf subalgebra `Aᵖ`, and the "kernel" appears only as
the QUOTIENT RING `A ⧸ I_{Aᵖ} A`, for which mathlib's `Ideal.IsHopfIdeal` + quotient instance
already suffice.  And the OTHER half of the theorem — the PBW/height-one half, which is where the
mathematics is — needs nothing new at all: every input is already sorry-free in this repository,
in `Fermat/FLT/GroupScheme/Cartier.lean`.
**THE CHEAPEST HALF-HOUR OF A THEORY-BUILD TASK IS SPENT FINDING A SOURCE WITH A COMPLETE PROOF,
AND THE ONE EVERY DOCSTRING CITES MAY BE THE PAYWALLED ONE.**  Four docstrings and the task prompt
cited Waterhouse GTM 66 ch. 14 and Demazure–Gabriel III §3 6.3; neither is obtainable (Springer and
Masson, and the ebin.pub mirror has been purged).  **Milne, *Algebraic Groups: The Theory of Group
Schemes of Finite Type over a Field*, CUP 2017, is FREE at `jmilne.org/math/Books/iAG2017.pdf`**,
carries the same theorem as **11.29** with a complete two-page proof, its ingredients as **11.27**
and **11.28**, the freeness input as **3.31** and the Frobenius-subalgebra input as **3.29** — and
the non-perfect-field COUNTEREXAMPLE as Exercise 11-3, which is Waterhouse ch. 14 Exercise 1.  It
is now at `~/flt-lean/sources/milne2017iag.{pdf,txt}` (Thm 11.29 at line 10752).  One `curl` and
one `pdftotext` turned a leaf whose stated cost was "define the Frobenius-kernel filtration" into
a two-leaf cut with the whole proof transcribed into the docstrings.
**So, before pricing any "missing theory" leaf: find a source that PROVES it, and prefer the free
one.**  Milne's site, Pink's ETH notes and Stacks are all one `curl` away; the Anna's Archive MCP
is NOT available to a loop-spawned agent (`ANNAS_KEY` is unset — confirmed again here), so the
open web is the route.  Download to `~/flt-lean/sources/` so the next agent does not pay twice.
### `Cartier.lean` IS THE PIN'S PBW ENGINE, and it is characteristic-free
`Fermat/FLT/GroupScheme/Cartier.lean` was written for a characteristic-ZERO theorem, and four
of its declarations are exactly Milne 11.25/11.27's tools, stated over an arbitrary field and
sorry-free: `CartierTheorem.pointDerivation` (the invariant derivation `A → A` attached to a point
derivation `A →ₗ K`, built as `(id ⊗ e_D) ∘ Δ` through the dual numbers — this is the ONLY place
the Hopf structure enters the height-one argument), `counit_pointDerivation` (`ε ∘ ∂ = D`),
`derivation_mem_pow` and `derivation_iterate_mem` (a derivation carries `J^(k+1)` into `J^k`).
`ModThree.lean` reaches them through `X0.lean:434`, with no import edit.  **When a leaf needs
"differentiate a Hopf algebra", look there before building anything.**
### FORMALISE ITERATED DERIVATIONS OVER MULTISETS AND LISTS, NOT OVER `Finset`-PRODUCT MONOMIALS
Measured on Milne 11.27, whose content is *`ε(∂_{i₁}⋯∂_{i_n}(x^{m}))` is `∏ mᵢ!` on the diagonal
and `0` off it*.  The obvious formalisation writes a monomial as `∏ i, x i ^ m i` and needs a
`Finset`-product Leibniz rule, `MvPolynomial.pderiv`, an iterated-`pderiv` coefficient formula and
`Nat.descFactorial` bookkeeping.  **None of that is necessary.**  Represent a monomial as a
MULTISET of variables, `xm x s := (s.map x).prod`; then
* the Leibniz step is `xm x (i ::ₘ s) = x i * xm x s` plus `Derivation.leibniz`, one line;
* the one-step congruence is `∂ᵢ (xm x s) − (count i s) • xm x (s.erase i) ∈ J ^ card s`, proved by
  a bare `Multiset.induction_on` with a two-way case split on `i = a`;
* iterate along a LIST (derivations do not commute, so the multiset will not do for the operator),
  carrying a coefficient `kap` defined by the same recursion, and the whole of Lemma 11.27 is
  `dl D L (xm x s) − kap L s • xm x (s − ↑L) ∈ J ^ (n+1)` for `card s = L.length + n`;
* `MvPolynomial` never appears, and the only thing needed about the coefficient is
  `¬ p ∣ kap L s` when `↑L ≤ s` and every `count i s < p` — a three-line induction over `p.Prime`,
  not the value `∏ mᵢ!`.
That development is 200 lines and compiles in ~30 s.  It is written out, verified sorry-free, in
`HANDOFF-modthree-heightone.md` at the repo root; the general lesson is that **when a proof is a
"differentiate a monomial `n` times" argument, the multiset presentation removes the combinatorics
rather than merely reorganising it.**
### AND THE FINAL ARGUMENT ONLY NEEDS THE MINIMAL-DEGREE TERM
The classical proof establishes that the degree-`n` monomials are a basis of `Iⁿ/Iⁿ⁺¹` and applies
it for each `n < p`.  For linear independence in `A` you never need the graded statement: take the
monomial of MINIMAL total degree with a nonzero coefficient, and apply `ε ∘ ∂_L` for a list `L`
realising it.  Terms of larger degree die from the FILTRATION alone (`dl_mem_pow`, no computation);
terms of the same degree die because `s − ↑L ≠ 0`.  One application, no induction over `n`.
