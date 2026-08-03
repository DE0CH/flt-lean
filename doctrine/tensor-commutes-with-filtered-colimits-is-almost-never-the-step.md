## "TENSOR COMMUTES WITH FILTERED COLIMITS" IS ALMOST NEVER THE STEP YOU HAVE TO FORMALISE

(2026-07-31, from closing Half A of [Stacks 00R6],
`exists_le_idealTensorComparison_eq_zero_of_isNoetherianFlatDescentSystem`.)

Several leaves in this development are cut with a docstring that ends "…tensor products
commute with filtered colimits, so the element already dies at a finite stage". Taken
literally that sentence is a whole module-theoretic colimit development — the colimit of
`↥(𝔪 C_j) ⊗_{C_j} D_j` over `j`, built from nothing but the ring-level `surj`/`sep`
fields — and `Ring.DirectLimit` is deliberately banned here, so there is nothing to build
it out of. A prover who takes it literally is looking at hundreds of lines before the
leaf's own argument starts.

**The substitute is mathlib's EQUATIONAL CRITERION FOR FLATNESS**,
`Module.Flat.isTrivialRelation_of_sum_smul_eq_zero` (`@[stacks 00HK]`, in
`Mathlib/RingTheory/Flat/EquationalCriterion.lean`). It converts flatness at the COLIMIT
into a **finite amount of data**: from `∑_k a_k x_k = 0` it returns `b_{kp}` and `y_p`
with `x_k = ∑_p b_{kp} y_p` and `∑_k a_k b_{kp} = 0`. Finite data is exactly what
`c_surj`/`d_surj`/`c_sep`/`d_sep`/`directed` descend, one element and one equation at a
time. No colimit of modules is ever constructed; only ring elements and ring equations
are ever moved. The whole colimit step came to ~90 lines.

Two things that fall out and generalise:

- **`exists_ub_finset_of_directed` / `exists_ub_fintype_of_directed`** (added to
  `AbelianSchemeIsogeny.lean`): pairwise directedness upgraded to finite sets and to
  fintype-indexed families, stated for a bare `le : Λ → Λ → Prop` with reflexivity,
  transitivity and directedness as arguments. Every descent argument in this development
  needs one, and there was none — check for them before writing a `Finset.induction` by
  hand. They apply verbatim to `NoetherianLocalBaseSystem` and `NoetherianLocalExtSystem`
  as well as to `IsNoetherianFlatDescentSystem`.

- **`M ⊗[R] S` is NOT an `S`-module in mathlib.** `TensorProduct.leftModule` acts on the
  LEFT factor; there is no right-hand counterpart, so a docstring step of the form "…so
  its submodule is f.g. because `D` is Noetherian", where the submodule sits inside
  `↥𝔪 ⊗[C] D`, is *not directly expressible*. The fix that worked, and it is reusable:
  present the tensor by TUPLES — if `I = (a_1,…,a_r)` then every element of `↥I ⊗[C] M`
  is `∑_k ⟨a_k⟩ ⊗ₜ x_k` (`exists_repr_tmul_of_span_range`) — and run the finite-generation
  argument on the kernel of an honestly `D`-linear map `D^r → D` instead. Do not go
  looking for `TensorProduct.rightModule`; it is not there.

