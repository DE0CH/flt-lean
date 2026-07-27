/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Ideal.Over

/-!
# The local criterion of flatness for a nilpotent ideal

Let `A` be a commutative ring, `J ⊆ A` an ideal with `J ^ N = ⊥`, and `B` an `A`-algebra.
Then `B` is flat over `A` as soon as

* `B ⧸ J B` is flat over `A ⧸ J`, and
* `Tor₁^A(A ⧸ J, B) = 0`, written without derived functors as injectivity of `J ⊗[A] B → B`.

This is [Stacks 00MK] / [Stacks 051C] in the nilpotent case, Matsumura *Commutative Ring
Theory* 22.1/22.3, Bourbaki *Algèbre commutative* III §5.  **No separatedness and no
Artin–Rees are involved** — that is the whole point of the nilpotent case, and it is why
this statement, rather than the full local criterion, is what the consumer needs.

## Why this is a leaf and not a proof

**There is no usable `Tor` in this pin** (checked 2026-07-27, and this is the whole
obstruction).  `Mathlib/CategoryTheory/Monoidal/Tor.lean` does define `Tor C n` as the left
derived functor of the tensor product, but the file is 60 lines long and its own module
docstring says "For now we have almost nothing to say about it!": there are exactly two
lemmas, both of the form "higher `Tor` of a projective vanishes".  In particular there is
**no long exact sequence**: `Mathlib/CategoryTheory/Abelian/LeftDerived.lean` constructs
`Functor.leftDerived` and `NatTrans.leftDerived` and stops — grepping it for
`ShortComplex.ShortExact` returns nothing, so there is no connecting map and no
`Tor₁ → ⊗ → ⊗ → ⊗ → 0` anywhere in the library.  `Mathlib/RingTheory/Flat/` has no `Tor`
at all and there is no `LocalCriterion` file in the library.

## Two routes for a prover, both real

**Route 1 — the classical one, over a small `Tor₁` API.**  It is two steps
([Stacks 00MK]), and each is short *once the long exact sequence exists*:

1. If `Tor₁^A(A ⧸ J, M) = 0` and `M ⧸ JM` is flat over `A ⧸ J`, then `Tor₁^A(N, M) = 0`
   for **every** `A ⧸ J`-module `N`.  Present `N` over `A ⧸ J` as `0 → K → F → N → 0`
   with `F` free over `A ⧸ J`; then `Tor₁^A(F, M) = ⊕ Tor₁^A(A ⧸ J, M) = 0`, and in the
   long exact sequence the next map `K ⊗_A M → F ⊗_A M` is `K ⊗_{A⧸J} M⧸JM → F ⊗_{A⧸J} M⧸JM`,
   injective because `M ⧸ JM` is `A ⧸ J`-flat.  Hence `Tor₁^A(N, M) = 0`.
2. For a general `A`-module `N`, filter by `J^i N`.  The filtration is FINITE because
   `J ^ N = ⊥`, every graded piece is an `A ⧸ J`-module, so step 1 plus the long exact
   sequence gives `Tor₁^A(N, M) = 0` by induction on the length.  Take `N = A ⧸ I` and
   apply `Module.Flat.iff_rTensor_injective'`.

   What has to be built for this route is exactly: `Tor₁` for modules (a presentation-based
   definition suffices), its independence of the presentation, and the six-term exact
   sequence in the FIRST variable.  That is a genuine theory build and it belongs here, in
   the shim tree, not in the consumer.

**Route 2 — elementary, no derived functors, over the equational criterion.**
`Module.Flat.iff_forall_isTrivialRelation` (`Mathlib/RingTheory/Flat/EquationalCriterion.lean`,
[Stacks 00HK]) says `M` is flat iff every relation `∑ f i • x i = 0` is *trivial*: there are
`a : ι → Fin k → A` and `y : Fin k → M` with `x i = ∑ j, a i j • y j` and `∑ i, f i * a i j = 0`.
The induction to run is on `r`, with the statement

  `∃ k (a : ι → Fin k → A) (y : Fin k → M), (∀ i, x i = ∑ j, a i j • y j) ∧ ∀ j, ∑ i, f i * a i j ∈ J ^ r`

— at `r = 0` take `k = |ι|`, `a` the identity matrix and `y = x`; at `r = N` the error lies in
`J ^ N = ⊥`, i.e. it is `0`, which is exactly triviality of the relation.  The inductive step
is where both hypotheses are spent: flatness of `M ⧸ JM` over `A ⧸ J` trivialises the relation
modulo `J`, and the `Tor₁` hypothesis converts the resulting annihilated element into a genuine
correction of the matrix `a`.  This is the route that needs no new theory, at the cost of
matrix bookkeeping.

## Faithfulness note on the shape of the statement

It is stated for an `A`-ALGEBRA `B` rather than for a bare `A`-module `M` for one reason only:
`Algebra (A ⧸ J) (B ⧸ J.map (algebraMap A B))` is an instance
(`Ideal.Quotient.algebraQuotientMapQuotient`), whereas `Module (A ⧸ J) (M ⧸ J • ⊤)` is not, so
the module form cannot even be *stated* without carrying a scalar action by hand.  The module
form is the one that belongs in mathlib, and a prover who produces it should restate this as a
corollary rather than duplicating the argument.

`htor` is written in the shape of `Module.Flat.iff_lift_lsmul_comp_subtype_injective`, i.e. as
injectivity of `TensorProduct.lift ((LinearMap.lsmul A B).comp J.subtype) : J ⊗[A] B → B`,
which is precisely `Tor₁^A(A ⧸ J, B) = 0` spelled without derived functors.

[Stacks 00MK]: https://stacks.math.columbia.edu/tag/00MK
[Stacks 051C]: https://stacks.math.columbia.edu/tag/051C
[Stacks 00HK]: https://stacks.math.columbia.edu/tag/00HK
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Module.Flat

/-- **THE LOCAL CRITERION OF FLATNESS FOR A NILPOTENT IDEAL** (sorry leaf — pure
commutative algebra; [Stacks 00MK] / [Stacks 051C], Matsumura *Commutative Ring Theory*
22.1/22.3).

`J ^ N = ⊥`, `B ⧸ JB` flat over `A ⧸ J`, and `J ⊗[A] B → B` injective (which is
`Tor₁^A(A ⧸ J, B) = 0` written without derived functors) together force `B` flat over `A`.

The module docstring above records the two routes to a proof, and why neither is a
one-liner at this pin: **mathlib has no `Tor` long exact sequence**, so the classical
argument has to be replaced either by a small `Tor₁` theory built here or by the
successive-approximation proof over `Module.Flat.iff_forall_isTrivialRelation`.

Consumed by `Fermat.flat_quotientMap_pow_of_flat_quotientMap`
(`Fermat/FLT/Modularity/AbelianSchemeIsogeny.lean`), which is the nilpotent half of the
one-element local criterion `Fermat.flat_of_flat_quotient_isSMulRegular`. -/
theorem of_flat_quotient_of_pow_eq_bot {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] (J : Ideal A) (N : ℕ) (hJnil : J ^ N = ⊥)
    (hflat : Module.Flat (A ⧸ J) (B ⧸ Ideal.map (algebraMap A B) J))
    (htor : Function.Injective
      (TensorProduct.lift ((LinearMap.lsmul A B).comp J.subtype))) :
    Module.Flat A B :=
  sorry

end Module.Flat
