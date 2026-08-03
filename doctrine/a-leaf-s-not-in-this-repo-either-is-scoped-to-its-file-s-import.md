## A LEAF'S "NOT IN THIS REPO EITHER" IS SCOPED TO ITS FILE'S IMPORT CONE — AND THE FIX MAY BE THREE `import` LINES
(2026-07-31, `flt-lean-1`, the two Shimura-algebraicity lattice leaves in
`X0.lean` and `X1.lean`.)  CLAUDE.md already records that an absence audit which
greps mathlib and `~/cs/FLT` must also grep `Fermat/`.  This is the sharper
variant, and it survives that correction: the audit **did** speak about this
repo, and was still wrong, because it was reasoning about what its own file can
NAME rather than about what the tree CONTAINS.
`exists_integralHeckeEigensystem_of_isWeightTwoEigenform`'s survey listed two
routes and dismissed the cheaper one with
> against it, `T_n` as an endomorphism of `CuspForm` does not exist in this repo
> either (only the coefficient relations inside `IsWeightTwoEigenform`), so it is
> not obviously the cheaper route.
Four things it names as absent are PROVEN, in `Fermat/FLT/Modularity/`:
`heckeOp : ℕ → ℕ → Module.End ℂ (CuspForm (Gamma0GL M) 2)` (`HeckeOperator.lean`),
its `q`-expansion formula `qCoeff_heckeOp` and the faithfulness of `q`-expansions
`cuspForm_eq_of_forall_qCoeff_eq` (`HeckeQExpansion.lean`), and — the one that
decides the route — `heckeOp_apply_eq_smul_of_isWeightTwoEigenform`, i.e. *`f` is
an eigenVECTOR of the operator*, not merely a solution of the coefficient
recursion (`HeckeAtkinLehner.lean`).  **`X0.lean` imports none of the three, and
all three import only mathlib and each other, so there is no cycle**; the two
`Gamma0GL`s are in different namespaces and are the same term, with a
machine-checked note in `WeightTwoEigenform.lean` recording that `heckeOp N n`
applies directly to a `CuspForm (Gamma0GL N) 2`.
**The tell, and it is what to grep for.**  A survey written inside a leaf
searches the vocabulary the leaf is stated in.  This leaf is stated in the
scheme-theoretic `X₀(N)` vocabulary, so its author searched for *homology*, and
the `CuspForm`-level clause was added as an aside about a route they were
declining.  So: **when a survey dismisses a route with one clause about an object
in a DIFFERENT vocabulary from the leaf, grep the whole tree for that object
before believing the clause** — one `grep -rn "def heckeOp\|Module.End ℂ (CuspForm"
Fermat/` would have settled it, and it costs a second against a route decision
worth a subtree.
Corollary about the shape of the repair, and it generalises: the answer is not
always "prove it" or "hoist it".  Here it is **three `public import` lines plus a
namespace check**, and the right deliverable from an agent that finds this but
does not have budget to take the import risk on a 119 000-line file is to write
the module names, the no-cycle check and the residual item list into the leaf's
docstring, where the next owner reads it.  An import audit recorded is worth more
than an import audit performed badly.
### `Basis` is `Module.Basis` at this pin, and the failure reads as a missing import
Cost one round.  `Basis`, `Basis.mk`, `Basis.coe_mk`, `Basis.repr_self` are all
under `namespace Module` (`Mathlib/LinearAlgebra/Basis/Defs.lean:76`), so writing
`Basis` — or even `_root_.Basis` — gives `Unknown identifier`, which is exactly
what a missing or mis-specified import gives, and sends you to the import block.
`Module.Basis` is the name.  `LinearMap.toMatrix`, `LinearMap.toMatrix_apply` and
`LinearMap.toMatrix_mulVec_repr` are NOT renamed, which is what makes the
namespace inconsistent-looking and easy to misdiagnose.
