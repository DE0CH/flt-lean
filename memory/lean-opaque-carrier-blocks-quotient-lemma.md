---
name: lean-opaque-carrier-blocks-quotient-lemma
description: A structure field whose carrier is an opaque CommRingCat carries Algebra.toModule, so a helper stated over a literal `A[σ] ⧸ I` never applies — state the helper with the carrier ABSTRACT
metadata:
  type: reference
---

A `NoetherianModelTower`-style field such as `isPushoutModT` is stated with `Mod i` an
opaque `CommRingCat`, so the instances baked into its type are `Algebra.toModule` /
`CommRing.toCommSemiring.toAddCommMonoid`. Instantiating `Mod i := CommRingCat.of
(MvPolynomial σ A ⧸ I)` does **not** re-run instance search — the goal keeps those. But a
helper lemma written with the carrier spelled literally as `MvPolynomial σ A ⧸ I` gets
`Submodule.Quotient.module'` and `Submodule.Quotient.addCommMonoid` instead. The two are
defeq only through `AddMonoidAlgebra.mul'`, which the module system does **not expose**,
so unification fails with a bare "application type mismatch" plus a note listing
unexposed definitions. No `show`, `convert`, or `@`-annotation fixes it.

**How to apply:** state the helper with the quotients ABSTRACT — carriers `C`, `D` with
`[Algebra A C]` etc., presented by ring maps `πC : MvPolynomial σ A →+* C` plus
surjectivity, `algebraMap` compatibility, and `RingHom.ker πD = (RingHom.ker πC).map
(MvPolynomial.map (algebraMap A B))`. Then every instance in the helper is
`Algebra.toModule` and matches the field syntactically. Prove bijectivity of
`Algebra.TensorProduct.lift` by building the inverse `D → B ⊗[A] C` by hand out of
`MvPolynomial.eval₂Hom` — going through `Algebra.TensorProduct.tensorQuotientEquiv` or
`MvPolynomial.algebraTensorAlgEquiv` reintroduces the quotient instances, and their
`Ideal.map_map` step also fails to `rw` because `includeRight` is an `AlgHom` where
`Ideal.map_map` wants a `RingHom`.

Second half of the same trap, and it bit first: `(bs.restrict i₀).Base i` and
`bs.Base i.1` are definitionally equal but **not syntactically** equal, and instance
search is syntactic — `Ideal.Quotient.mk` could not synthesize `Ideal.IsTwoSided` across
the two spellings. Fix by writing the whole construction over a bare system with a bottom
index, `(bs, b₀, hb₀ : ∀ i, bs.le b₀ i)`, and instantiating at
`(bs.restrict i₀, ⟨i₀, le_rfl⟩, fun i => i.2)`; that deletes every `.1` and every
`restrict` from the interior. Doing this closed
`exists_noetherianModelTower_of_finitePresentation` after both spellings had failed.

Related: [[lean-module-system-elides-proof-bodies]], [[flt-two-leaves-may-be-one]].
