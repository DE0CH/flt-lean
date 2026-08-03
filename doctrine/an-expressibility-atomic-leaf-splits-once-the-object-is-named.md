## AN "EXPRESSIBILITY-ATOMIC" LEAF SPLITS ONCE THE OBJECT IS NAMED — AND THE PIN TRAVELS AS A **PREDICATE**, NOT AS A CARRIER
(2026-07-31, `flt-lean-177`, `nonempty_modularTateCarrierData_of_mult` in
`Modularity/Interface.lean`, PROVEN over three leaves.)
The section above on expressibility cuts says: when a leaf's own docstring reports that a
split "cannot be stated" or "would manufacture a false leaf", the task is to BUILD THE
OBJECT rather than to attack the mathematics. This is the sequel — what to do at the NEXT
cut, once the object exists — and it is a shape that recurs wherever a leaf bundles several
classical theorems about one unconstructed carrier.
The trap the previous cutter correctly identified: a sub-leaf that receives an ABSTRACT
carrier `Vp` satisfying the formal clauses is FALSE, because Eichler–Shimura holds for the
Tate module of `J₀(M)` and not for an arbitrary faithful Hecke module of the right
dimension. So every residue has to be stated over the PINNED object.
**The move that makes three leaves out of one is to pin with a FRAME plus a named
PREDICATE, and never with a carrier.**
* Leaf (A) produces an integral frame: `τ : GaloisRep ℚ ℤ_[p] (Fin n → ℤ_[p])` together
  with a bijection `φ` onto the pinned `TatePt …` intertwining addition and Galois. `φ` is
  the pin: any later leaf that mentions `φ` is talking about the genuine Tate module.
* Leaf (C) produces the operator algebra AND a predicate `IsFrameHeckeAction` saying that
  `act (1 ⊗ T_q)` carries the integral lattice into itself and is, read through `φ`,
  postcomposition by the SCHEME MORPHISM `T q`.
* Leaf (B) RECEIVES `act` together with that predicate. That is what makes its conclusion
  (Rosati self-adjointness of the twisted pairing) a theorem rather than an assumption:
  the predicate determines `act` on the generators, `adjoin_modularTateGen_eq_top` says
  the generators generate, so `act` is determined outright.
**The check that licenses a "receives it as a hypothesis" leaf is exactly that
determinacy argument, and it must be written down.** Ask: does the pin plus the frame's
injectivity fix the received datum uniquely? If yes, the receiving leaf is honest; if no,
you have handed a prover an under-pinned object and the leaf is refutable by whatever the
pin fails to exclude. Here the argument is three lines and it is in the predicate's
docstring.
**AND THE PIN PAYS FOR ITSELF IMMEDIATELY: one whole clause came out of the leaves.**
`hecke_comm` ("Hecke correspondences are defined over `ℚ`, so `T_q` commutes with Galois")
is not a theorem anybody needs to prove. `RelPoint.post u` is `· ≫ u` and the Galois action
on geometric points is `Spec σ ≫ ·`, so the two commute by **`Category.assoc`**. Transport
that along the frame and it says `act` and the base-changed `τ` commute on the lattice.
So: **after pinning a leaf geometrically, re-read the remaining clauses and ask which of
them are now associativity.** In a functor-of-points development the answer is usually "at
least one".
### The reusable half: `ℤ_p`-frame ⟶ `ℚ̄_p`, and the lattice trick
Three small definitions do all the base-change bookkeeping the eighteenth cut's docstring
had budgeted for, and they are worth copying verbatim:
    qbarFrameEquiv p n := ((Pi.basisFun ℤ_[p] (Fin n)).baseChange (AlgebraicClosure ℚ_[p])).equivFun
    qbarRep τ         := (τ.baseChange (AlgebraicClosure ℚ_[p])).conj (qbarFrameEquiv p n)
    qbarIncl p n u    := fun i => algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) (u i)
`GaloisRep.baseChange` needs `ContinuousSMul ℤ_[p] (AlgebraicClosure ℚ_[p])`, which is NOT
a global instance — supply `continuousSMul_padicInt_algebraicClosure` with a `letI` inside
the definition; it is a `Prop` class, so proof irrelevance makes later unfolding painless.
**The lattice trick is the part that generalises furthest.** To say "this `ℚ̄_p`-linear map
is the base change of an integral one" you do not need a `Submodule`, a lattice type, or
any `IsScalarTower` plumbing: state it on `qbarIncl p n u` for all `u`, and prove once that
* `qbarRep τ γ (qbarIncl p n u) = qbarIncl p n (τ γ u)` — via
  `Module.Basis.baseChange_repr_tmul` and `Algebra.algebraMap_eq_smul_one`;
* `qbarIncl p n (Pi.single i 1) = Pi.single i 1`, so the lattice CONTAINS the standard
  basis and two `ℚ̄_p`-linear endomorphisms agreeing on it are equal
  (`Module.Basis.ext (Pi.basisFun …)`).
Those two lemmas are ~10 lines each and they are what let leaf statements about integral
data and leaf statements about `ℚ̄_p`-linear data live side by side with no transport.
Two mechanical notes: `Module.End`'s multiplication unfolds with **`Module.End.mul_apply`**
(there is no `LinearMap.mul_apply` at this pin), and
`(algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p])).injective` demands an `IsSimpleRing ℤ_[p]`
instance that does not exist — use this tree's
`algebraMap_padicInt_algebraicClosure_injective`.
### Assemble the exceptional set from the leaves, do not guess it
`ModularTateCarrierData` carries ONE `S : Finset (HeightOneSpectrum …)` used by two
different clauses (`congruence` and `pair_frob`) proved by two different leaves. Do not
make one leaf guess a set that also has to work for the other: let each leaf produce its
OWN exceptional set and let the glue take `S := SB ∪ SC`. Both clauses then follow from
`Finset.mem_union_left/right` in one line each. Same recipe for any structure field that
several leaves must respect a common bound on.
### Accounting, stated the way the doctrine asks
`1 → 3`, i.e. `+2` on the direct-sorry count (`Interface.lean` 16 → 18, tree 372 → 374,
measured from the build's own warning set before and after). That is the honest number and
the cut is still right: what left the frontier permanently is the base-change glue, the
`hecke_comm` clause, and the exceptional-set bookkeeping, and each of the three residues is
one classical theorem with a citation (Mumford §18 / Silverman III.7; the Rosati involution
of the Atkin–Lehner-twisted polarization; Igusa and Diamond–Shurman 8.6.1, 8.7.2). Judge by
what is LEFT in each leaf.
