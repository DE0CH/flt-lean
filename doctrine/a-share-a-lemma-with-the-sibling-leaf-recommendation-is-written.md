## A "SHARE A LEMMA WITH THE SIBLING LEAF" RECOMMENDATION IS WRITTEN FROM THE STRONGER SIBLING'S ROUTE
(2026-08-02, `flt-lean-377`, `isUnit_det_of_pderiv_eq_three_mul` in
`GaloisRepresentation/HardlyRamified/ModThree.lean`.)  When one audit item is cut
into two sibling leaves that both mention the same object, the docstring routinely
ends *"an owner proving both leaves should expect to share a lemma between them —
hoist `<the statement>` as its own named leaf."*  That sentence names the lemma
**the author's own route for the HARDER sibling uses**, and it is written before
anybody has asked what the EASIER sibling consumes.  Here it named
> `Ω[B⁄𝒪₃ᵥ]` is free of rank `h` over `B/3B`
which item 2 genuinely needs (it compares lengths over the artinian `B̄`) and item
6 does not need **at all**.  Item 6's whole content is `3·Bʰ ⊆ Jac(P')`, which is
`hΩ` read through the presentation `Ω = Bʰ/Jac`; after that it is a scalar
cancellation and a matrix identity.  A successor who had obeyed the docstring
would have built a rank-and-length argument for nothing.
**The check costs one careful read and it is not the one the docstring invites.
Write down, separately, what each sibling's conclusion CONSUMES — then compare.**
Two refinements that both mattered here:
* the genuinely shared fact was one level down (the PRESENTATION `Ω = Bʰ/Jac`,
  not its freeness), and
* the two siblings need DIFFERENT HALVES of even that.  Item 2 reads it as an
  EQUALITY; item 6 needs only `N ⊆ Jac` — the inclusion proved by the plain
  Leibniz rule, since every polynomial relation is a finite `R`-combination of the
  `P'ᵢ` and `α(P'ᵢ) = 0`.  The reverse inclusion is the one needing a limiting
  argument (the `P'ᵢ` are power series, not polynomials) and it is not used.
So a shared-lemma recommendation should be read as *"there is something shared,
go and find out what"*, never as a specification.  Same family as
[[flt-leaf-cost-estimates-are-hypotheses]], with the hypothesis being about a
SIBLING's needs rather than about the pin.
### "SURJECTIVE ENDOMORPHISM OF A FINITE MODULE" IS THE LONG WAY TO A UNIT DETERMINANT
Same leaf, and it is worth reaching for directly whenever a route ends *"…so the
matrix is a surjective endomorphism of a finite module, hence an isomorphism,
hence its determinant is a unit."*  **If you know the rows span, the span
COEFFICIENTS are already a left inverse.**  `Submodule.mem_span_range_iff_exists_fun`
hands you `c` with `∑ᵢ cⱼᵢ • Mᵢ = eⱼ`; assembling `N := Matrix.of c` gives
`N * M = 1` by `Matrix.mul_apply` alone, and `det N * det M = 1` finishes.  No
`Module.Finite`, no Nakayama, no injectivity step — and the resulting lemma is
stated over an ARBITRARY commutative ring, so it is reusable where the finiteness
hypothesis would not have been available.
Three pin-level facts that cost a round each:
* **`isUnit_of_mul_eq_one` does not exist at this pin.**  The name is
  `IsUnit.of_mul_eq_one (b : M) (h : a * b = 1) : IsUnit a`, gated on
  `[IsDedekindFiniteMonoid M]`, which every `CommRing` supplies.
* **`Submodule.mem_span_range_iff_exists_fun` takes the RING EXPLICITLY.**
  `Submodule.mem_span_range_iff_exists_fun.mp` is an `Unknown constant`; write
  `(Submodule.mem_span_range_iff_exists_fun C).mp`.
* **`3` is a nonzerodivisor on an IDEMPOTENT quotient with no splitting
  machinery.**  `Module.Flat.isSMulRegular_of_nonZeroDivisors` gives it on `A`
  (`𝒪₃ᵥ` is a `CharZero` domain, so `(3 : 𝒪₃ᵥ) ∈ nonZeroDivisors` by
  `mem_nonZeroDivisors_iff_ne_zero.mpr (by norm_num)`), and for `J = (ε)` with `ε`
  idempotent the transfer is one line: `3a = cε` gives
  `3·a(1−ε) = c(ε − ε²) = 0`, so `a(1−ε) = 0`, so `a = aε ∈ (ε)`.
  `AlgEquiv.prodQuotientOfIsIdempotentElem` and the decomposition
  `A ≅ A⧸(ε) × A⧸(1−ε)` are not needed; `hidem` is spent as an EQUATION.
  Watch the scalar-versus-ring `3`: `(3 : 𝒪₃ᵥ) • a` becomes `(3 : A) * a` by
  `simp only [Algebra.smul_def, map_ofNat]`, and the `𝒪₃ᵥ`-side `≠ 0` must be
  pinned with a `show`, or the `norm_num` fires on a metavariable.
