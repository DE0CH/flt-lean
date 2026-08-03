## A PRODUCT OVER "REDUCED REPRESENTATIVES" IS NOT A PRODUCT OVER CLASSES — AND A TRANSVERSAL IS CHEAPER THAN A UNIQUENESS THEOREM
(Same task, and it would have made the new leaf FALSE.) A statement of the form *"`∏_{f ∈ F}
(X − φ(f))` has rational coefficients"* — a class equation, an orbit polynomial, a norm over a
Galois orbit — is true for `F` a set of representatives meeting each class **exactly once**, and
FALSE for a set that repeats a class. The trap is that the obvious candidate for `F` is the set
cut out by the file's own normal-form predicate, and that predicate is routinely stated in a
WEAKENED form because its full normalisation was never needed before.
Here `IsReduced` is `|b| ≤ a ≤ c` and its docstring says plainly that it omits the `b ≥ 0`
tie-break "which is not needed for anything below". So at `d = −23` both `⟨1, 1, 6⟩` and
`⟨1, −1, 6⟩` are reduced and properly equivalent, the principal class is counted twice, and the
product acquires an extra irrational factor `X − j(τ₀)`: numerically
`X⁴ + 6984975.69996993…X³ + ⋯` against the true `X³ + 3491750X² − 5151296875X + 12771880859375`.
A leaf stated over "the reduced forms" is refutable at the smallest discriminant with `h > 1`.
**Two things follow, and the second is the reusable one.**
* **Check the normal-form predicate for a dropped tie-break before quantifying over it.** The
  tell is a docstring sentence of the form "the extra normalisation is not needed for anything
  below" — true when written, and load-bearing the moment somebody forms a product.
* **You do not need the uniqueness theorem. Take a TRANSVERSAL.** Proving that the normalised
  reduced form is unique in its class is Gauss's theorem, a real case analysis. Picking one
  element per class out of a FINITE set is 25 lines of `Finset.strongInduction`: take `x ∈ S`,
  recurse on `S.filter (¬ x ~ ·)`, insert. It needs only reflexivity, symmetry and transitivity
  of the relation, and it hands you both clauses a class equation wants — pairwise
  inequivalence and completeness — with no normal form mentioned anywhere.
Corollary for the STATEMENT: make "exactly one per class" a HYPOTHESIS of the leaf
(`hindep` + `hcomplete`) rather than baking a particular representative set into it. Then the
leaf is about the mathematics, the transversal is a separate proven theorem, and — the part that
matters for a falsity audit — each clause can be shown load-bearing by a witness, which is how
the two above were verified rather than assumed.
