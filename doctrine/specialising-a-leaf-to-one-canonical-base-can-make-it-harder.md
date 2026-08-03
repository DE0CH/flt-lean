## SPECIALISING A LEAF TO ONE CANONICAL BASE CAN MAKE IT HARDER — check the citation's own proviso

(2026-07-31, `flt-lean-19`.) A cut that replaces "for every `R`" by "at the one canonical `R`"
reads as a strict improvement, and the tie-breakers above endorse it: same leaf count, one
instance instead of a family, and "a citation instantiated once is what the citation IS". That
reasoning is right whenever the citation applies at the chosen base. **It is exactly backwards
when the chosen base is the one where the citation's own hypotheses fail.**

`nonempty_gamma0AtlasOver_specLoc` (Katz–Mazur (8.1.1), the `Γ₀(N)`-atlas) was specialised on
2026-07-29 from "every `R : Subring ℚ`" to `ℤ`, with every other subring recovered by flat base
change — `ℤ → R` is flat for all of them, so the derivation is four lines and the cut looks free.
But Katz–Mazur construct `M(𝒫)` under an explicit proviso — *"to define `M(𝒫)` as an `R`-scheme it
suffices to do so locally on `R`, so we may assume some integer `n ≥ 3` is invertible in `R`"* —
and `ℤ` is the **unique** subring of `ℚ` where no `n ≥ 3` is invertible. Every other base
satisfies the proviso outright. So the specialisation silently folded a two-chart Zariski gluing
of the ENTIRE atlas (`Y`, the classifying map, the fppf cover *and* the categorical quotient,
over `D(3)`, `D(5)`, glued along `D(15)`) into a leaf whose docstring still described it as the
citation. The leaf's own text even named the gluing — "where the whole cost of a non-local base
sits" — without drawing the conclusion that this made the leaf strictly harder than the family it
replaced.

Two rules come out of it, and the second is the transferable one.

**1. Before specialising to a canonical instance, check the source's hypotheses AT that instance.**
"Every base is a flat base change of `B`" makes `B` a sufficient base *logically*; it says nothing
about whether the theorem you are citing is proved at `B`. Degenerate/extremal bases — `ℤ`, a
field of small characteristic, `N = 0`, the trivial group — are exactly where citations carry
provisos, and they are exactly the bases a "one canonical instance" argument selects for.

**2. A hypothesis the CONSUMERS already hold costs nothing, and this is worth checking BEFORE
inventing machinery to avoid it.** The repair here was to give the leaf Katz–Mazur's own proviso
(`∃ n ≥ 3, IsUnit (n : R)`) and thread it through three intermediate theorems that lacked `ℓ` in
scope. Every terminal consumer already carried `IsReductionBase ℓ R toF`, which forces `R = ℤ_(ℓ)`
and hence supplies the proviso (`n = 3`, or `4` at residue characteristic `3`) — so the leaf got
strictly weaker and no consumer's statement changed. Same shape as
`exists_artinDivisorNormIndex_le_ray_class` above: *the missing hypothesis is usually already in
the caller's hand, and the reason it is not in the statement is that an intermediate theorem
discarded it.* Trace the consumer chain to its terminal hypotheses before concluding a leaf must
be stated in the generality it currently is.

Corollary for the generality question in general: the right test is not "which statement is more
canonical" but **"at which bases is the cited proof actually run"**. Quantifying over a family of
bases where the citation applies is CHEAPER than one base where it does not, however inelegant the
family looks.

