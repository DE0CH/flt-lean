## A SECOND OBJECT IN A LEAF'S HYPOTHESES MAY BE REMOVABLE BY AN ALREADY-PROVEN TRANSPORT
(Same task, and it is what made the cut worth making.)  The leaf took TWO data `d, d'`,
an isogeny pair `IsNIsogenyPair 169 d d'` and an isomorphism `IsBaseChangeOf (𝟙 _) d d'`
— the faithful transcription of "fixed by `w_N`", and three binders a prover has to
juggle before any mathematics starts.  One line deletes `d'`:
    hpair.baseChange (IsBaseChangeOf.refl d) hiso : IsNIsogenyPair 169 d d
`IsNIsogenyPair.baseChange` was proven days earlier for an unrelated consumer
(`AtkinLehnerMorphism.dual_baseChange`), and `IsBaseChangeOf.refl` likewise.  The
residue — *a datum `169`-isogenous TO ITSELF has irrational `j`* — is the classical
Fricke statement with nothing else in it.
**So before writing a leaf with two copies of an object related by an isomorphism, look
for the file's own transport calculus** (`.baseChange`, `.refl`, `.symm`, `.comp` on the
relation in question).  In this development those exist for almost every relation,
usually declared far from the leaf and under a name sharing no keyword with it — here
1 400 lines above, found by grepping `IsNIsogenyPair\.` rather than by grepping the
leaf's vocabulary.  The gain is not the binder count: it is that "isogenous to its own
quotient, which is isomorphic to it" and "isogenous to itself" read as different
problems to the next owner, and only the second is a statement they can look up.
