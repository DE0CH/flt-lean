## TWO WAYS TO CUT A LEAF THAT LOOKS ATOMIC (2026-07-31, both worked first try)

Both came out of `ModularCurve/RelativePicard.lean`, both closed a leaf the same
day, and both are cheap enough to try BEFORE concluding a node is irreducible.

**1. The leaf's own audit may misattribute where a hypothesis's content comes
from — and separating the two IS the cut.** `nonempty_modPullback_sectionIdeal`
was priced as "`φ^*` does not commute with a kernel; the content is that `D_x`
is FLAT over `T`, which is the content of `isInvertibleSheaf_sectionIdeal` (an
effective relative Cartier divisor is flat over the base)". The last clause is
**false**: invertibility of the ideal is Cartier-ness and says nothing about
flatness. Witness — `T = Spec k[s]`, `Y = Spec k[s,t]`, `D = V(st)`: the ideal
`(st)` is invertible (`st` is a nonzerodivisor) and `D` is not flat over `T`
(`s·t = 0` with `t ≠ 0`). The flatness actually came from a hypothesis the audit
never mentioned — `x` is a **section**, so `D_x ≅ T` over `T`. Once the two
inputs were seen to be independent the leaf split with nothing left over:
invertibility stayed a leaf, flatness became one `pullback.lift_snd`, and the
residual statement lost every mention of a curve (it is now Stacks 062Y/0631
over an abstract cartesian square). So: read a leaf's audit for sentences of the
form "X is the content of Y", and **check them**. A wrong one is a cut line.

**2. Never ask a geometry leaf to produce a bundled algebraic structure.**
`exists_relPicZeroSubgroup` asked for an `AbelianSchemeStruct` on `Pic⁰` —
twelve fields, of which nine are group axioms and two naturality. Not one of the
nine is about the identity component; they are the group axioms of `Pic`,
restricted to a subgroup, so the geometry's owner had to reprove them from
scratch. Replace the structure with **closure clauses** — the image contains the
zero point and is closed under addition and negation, each a bare existential
with no equation to verify — and transport the structure along the injection:
`ab.add p q` is the unique preimage (existence from closure, uniqueness from
injectivity), and every axiom is `inj` applied to a rewrite chain ending in the
corresponding law upstream.

The prerequisite is that the upstream laws exist. Here they did not, and proving
them was the bulk of the work — but each was `hP.inj` applied to a chain of
`RelPicEquiv`s (unitor, associator, braiding, `exists_modTensor_inv`), and all
six elaborated on the first attempt. **Generalisable rule: whenever a leaf's
conclusion contains a bundled structure, ask which fields are INHERITED rather
than constructed. Inherited fields belong in the assembly, never in the leaf.**

Corollary for bookkeeping, since neither cut moved the direct-sorry count: a cut
is one leaf closed and one opened, net zero. **Reading the count alone reports
that nothing happened.** Judge a cut by whether the open statement got smaller —
here one lost every mention of a curve and the other lost nine group axioms —
not by the delta.

**Pin trap found on the way**: `pullback.lift_fst` / `lift_snd` are `@[reassoc]`
but **not** `@[simp]` at `a3364fa`. A plain `simp` on a goal full of
`pullback.lift` silently does nothing and reports "unsolved goals" with the goal
unchanged, which reads as "this is hard". Name them in the simp set.

