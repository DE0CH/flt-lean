## GREP `Fermat/` FOR YOUR OWN LEAF'S NAME — the module built to serve you names you, and nothing tells you
(2026-08-02, `flt-lean-266`, `card_jacobian_of_isWeilEigenvalues` in `X0.lean`.)
This file already carries five sections on stale "MISSING MACHINERY" lists, and
they all prescribe the same repair: grep for the MACHINERY, over `Fermat/` and
not only over mathlib. That is right and it is the harder half of the search,
because you have to guess what the machinery would be called. **There is an
easier check that nobody runs, it is one command, and it points the other way:**
    grep -rn '<yourLeafName>' --include=*.lean Fermat/ | grep -v '<your own file>'
That leaf's docstring carried a four-item `WHAT IS MISSING` list dated
2026-07-30 whose items 1 and 2 — "divisors on a curve as a `Scheme`, their
degree and linear equivalence" and "Riemann–Roch attached to a `Scheme`" — were
already false when I read them. `Fermat/FLT/Mathlib/AlgebraicGeometry/CurveGenus.lean`
supplies `IsDivisorOn`, `divisorDegree`, `pointDivisor`, `IsCurveGenus` and the
named leaf `exists_isCurveGenus` (Riemann's theorem); `PrincipalDivisorDegree.lean`
supplies `Scheme.ord`, `Scheme.Hom.divDegree` and a PROVEN `divDegree_eq_zero`.
**Both were already `public import`s of `X0.lean`.** And `CurveGenus.lean`'s own
module docstring says, in as many words, that its contents are
> precisely the input to the Abel–Jacobi and point-counting arguments in
> `ModularCurve/X0.lean` (`card_jacobian_of_isWeilEigenvalues`)
— i.e. **the machinery names the leaf while the leaf says the machinery is
missing.** Neither author did anything wrong: the module was written for this
consumer by someone who could not edit a leaf they did not own, and the leaf's
docstring is frozen at the moment it was cut.
**Why the prescribed refuting check does not catch it.** That docstring's own
check is "a `grep` for the named notion over `.lake/packages/mathlib`, `Fermat/`
and `~/cs/FLT`", which is exactly correct — and what you grep for is the NOTION
(`RiemannRoch`, `divisor`, `genus`), which in this tree is filed under the
vocabulary of whoever built it, not yours. `grep -rli riemannroch` over mathlib
returns nothing and always will; it is the true clause that makes the false ones
look checked. Your own leaf's name, by contrast, is a string you cannot get
wrong, and a hit is never a coincidence.
So run BOTH, and run the cheap one first. A hit outside your own file is one of
exactly three things, all of which you need to know before your first edit: a
CONSUMER (so the leaf is live), a RIVAL CUT, or — the case this section is
about — **a module that was built to serve you and that nobody told you about.**
### Two riders from the same run
* **State a cardinality-comparison leaf as a BIJECTION, not as `Nat.card A =
  Nat.card B`.** `Nat.card` of an infinite type is `0`, so the equality form is
  discharged by BOTH sides being infinite — and at a freshly cut leaf neither
  finiteness is usually available, so that is not a hypothetical. `Nonempty (A ≃ B)`
  has no such escape, and it costs the consumer one `Nat.card_congr`. Here the
  geometric half `J(𝔽_ℓ) ≅ Pic⁰(X/𝔽_ℓ)` is stated that way for exactly this
  reason, while the arithmetic half keeps the `Nat.card` form BECAUSE there it is
  load-bearing in the good direction: its right-hand side `∏ (1 − αᵢ)` is a
  nonzero integer, so the equation genuinely ASSERTS finiteness rather than
  tolerating its failure. **Ask which side of the equation can be zero for the
  wrong reason**; that decides the shape.
* **A cut whose two halves land on opposite sides of an import edge is still the
  right cut — state the residue so it can be HOISTED, and say so.** The
  arithmetic half here is ~90% proven in `Modularity/Interface.lean` (steps 1, 2
  and 4 of the zeta chain, all PROVEN), and `Interface.lean` `public import`s
  `X0.lean`, so none of it is citable. Do not duplicate it and do not pretend the
  leaf is closed. Note also that no DUPLICATION of statement exists even so:
  Interface's `h` is existentially bound and its own docstring warns it is
  unpinned and is NOT `FunctionField.classNumber`. So the honest deliverable is a
  residue stated in vocabulary that mentions no modular curve and no Jacobian —
  which is then the one statement that would pin Interface's `h` too, once
  somebody hoists the zeta block to a module upstream of `X0.lean`.
