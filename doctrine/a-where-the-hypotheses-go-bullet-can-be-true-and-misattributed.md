## A "WHERE THE HYPOTHESES GO" BULLET CAN BE TRUE AND MISATTRIBUTED — NAME THE GENERAL THEOREM
(2026-07-31, `flt-lean-377`, on `exists_dualPolarization_finiteBase` in `TateModule.lean`.)
This development writes a `WHERE THE HYPOTHESES GO` list on most mature leaves, and those
lists are the first thing a successor reads. They are reliable about which hypotheses are
USED and unreliable about WHY, in a specific and repeatable way: the author names the
property the hypothesis is present for, and does not check whether that property needs it.
The bullet here read, in full and correctly:
> `hfin` also does real work of its own: over a FINITE field an abelian variety is
> projective and carries an ample line bundle DEFINED OVER `k`, so averaging
> `λ = Σ_i â_i ∘ λ₀ ∘ a_i` over a `ℤ`-basis of `𝒪_D` gives an `𝒪_D`-linear polarization
> over `k`, which is the `Γ_k`-equivariance clause.
Every clause is TRUE. The word FINITE is doing nothing in any of them: **an abelian variety
over ANY field is projective over that field** (Milne *AV* I.7.1, Mumford *AV* §6). The
route the same docstring prescribes for the equivariance clause — `Hom^sym` is finitely
generated with a continuous `Γ_k = Ẑ` action, so a power of Frobenius fixes a polarization
and its orbit sum descends to `k` — is a DESCENT from `k̄`, and there is nothing to descend,
because the polarization is already over `k`. Finiteness was buying exactly one thing,
`q ≠ char k`, and only through `hqN`.
**The check is one question per bullet, and it is not "is this sentence true":** *name the
general theorem the property comes from, and read off its hypotheses.* If the general
theorem holds without the hypothesis the bullet credits, the bullet is misattributed and the
leaf is stated in the wrong generality. Here that turned four binders (`hfin`, `N`, `hN`,
`hqN`) into one (`(q : k) ≠ 0`), with the four re-derived in three lines at the wrapper, so
the consumer did not move — a 1 → 1 recut whose residue is the statement the literature
actually proves.
**Watch for the tell: a bullet that says a hypothesis does work "of its own".** That phrase
marks a use the author added because the hypothesis was in scope, not because the
mathematics asked for it — which is precisely the use that a general theorem deletes.
