## A "CITE THEOREM X" ROUTE NOTE MUST BE CHECKED AGAINST THE TREE'S OWN DEVELOPMENT OF X — WHICH MAY BE HALF-BUILT, AND MAY CONSUME YOUR LEAF
(2026-07-31, `flt-lean-167`, on `HardlyRamified/NormIndex.lean`'s norm-index
inequality `n ≤ h`.) A mature leaf often carries a ROUTE INVENTORY that prices
each way in, and one entry is usually *"cite theorem X, which this project has
already paid for once"*. That entry is the one to re-derive, because it is a
claim about **where X lives and how far along it is**, and both halves rot.
Here the inventory said route 3 was "cite RECIPROCITY — which is what this
project has ALREADY done at modulus `1`", pointing at
`Fermat/FLT/NumberField/ArtinSymbol.lean`, and concluded that taking the
containment route would be a REGRESSION (one leaf for one strictly harder leaf)
unless the same citation also discharged that file's `artinMap_toPrincipalIdeal`.
Both clauses were true and the conclusion was wrong, for two independent reasons
that are worth checking separately on any such note.
**1. THE TREE MAY ALREADY BE BUILDING X, UNDER NAMES THAT SHARE NO KEYWORD WITH
X.** `ModThree.lean` — the file `NormIndex.lean` had just been hoisted OUT of —
carries ~13 000 lines of ray-class Artin reciprocity in exactly this formalism,
following Childress ch. 5, under names beginning `artin…_ray_class`. **Not one
of them contains the word "reciprocity"**, so an inventory that greps the
concept finds the other cluster and stops. What made the recut affordable was
that the CYCLOTOMIC BASE CASE of the wanted statement is PROVEN there
(`artinSymbol_span_eq_one_of_cyclotomic_ray_class`, and its divisor form), as is
the descent apparatus (`exists_artinAuxiliaryNumberField_ray_class`,
`exists_relNormDivisorHom_ray_class`). So the residual is one assembly, not a
theory. **Grep for the CITED THEOREM'S BASE CASE and for its standard proof's
auxiliary objects, not for its name** — a half-built development is invisible to
a name search and is exactly what changes the price.
**2. A TWO-SIDED THEOREM CAN HAVE ONE SIDE BUILT AND THE OTHER SIDE CONSUMING
YOUR LEAF.** Reciprocity here is two containments. The in-tree development proves
`ker ⊆ ray · norms` — and `exists_artinNormSubgroups_ramified_ray_class` takes
`hidx₂ : A.relIndex Im ≤ (P ⊔ N).relIndex Im`, *the target leaf's own
conclusion*, as a HYPOTHESIS. So citing that theorem to prove the leaf is
circular, while the OTHER containment (`ray ⊆ ker`) is used by nothing in it and
is free to cite. **Before citing a development, grep its BINDER LIST for your
leaf's conclusion**; a cluster that consumes you looks identical, from the
outside, to one that would serve you.
**Corollary for the recut that follows: cite the HALF, not the theorem.** The
new leaf is `ray ⊆ ker` alone — no Artin map, no surjectivity, no reverse
inclusion — so the "strictly harder leaf" objection does not apply to it even
though it does apply to full reciprocity. When a route note prices a citation,
check whether the proof needs all of the cited statement; here it needed one of
two containments, and that is the difference between a regression and a
decomposition.
### AND BEFORE PROMISING `2 → 1` ACROSS TWO MODULES, COUNT THE BRIDGES
The same task was dispatched to unify this leaf with `ArtinSymbol.lean`'s
`artinMap_toPrincipalIdeal` over one shared statement. **It is not available, and
the reason is structural rather than effort.** The two clusters are written in
two formalisms — `ArtinSymbol.lean` is deliberately mathlib-only (`frobAt`,
`Algebra.IsUnramifiedAt`, an abstract `L` with `[IsGalois K L]`), everything in
the `ModThree` cluster is absolute-Galois (`Γ F`, `globalFrob`,
`localInertiaGroup`) — and a shared citation needs a DICTIONARY between them.
Enumerated, that is four bridges, of which one exists:
* Frobenius: `restrictNormalHom L (globalFrob v) = frobAtBelow K L v` —
  **available**, `Chebotarev.lean`'s `exists_isArithFrobAt_restrictNormalHom_globalFrob`
  is PROVEN pointwise at every `v` with no unramifiedness hypothesis;
* finite inertia: `Algebra.IsUnramifiedAt (𝓞 K) Q` ⟹ the image of
  `localInertiaGroup w` in `Gal(L/K)` is trivial — **absent**;
* archimedean: `IsUnramifiedAtInfinitePlaces` ⟹ the character kills the
  decomposition group at each real place — **absent**;
* transport of an abstract Galois `L/K` into `IntermediateField K (AlgebraicClosure K)`
  — **absent**.
Two of the missing three are theorems of the same order as the leaves they would
serve, so the promised `2 → 1` is really `2 → 3`. **So the check before accepting
any cross-module unification task is to list the vocabulary of each side's
statement and ask which dictionary entries exist.** It costs one pass over two
signatures, and it is the difference between a decomposition and a several-
thousand-line regression. When the answer is negative, the useful output is the
BRIDGE LIST — the missing entries are usually wanted by several leaves each, and
building the cheapest one first is a better task than the unification was.
