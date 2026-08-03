## THE CONSTANT SHEAF `𝒦_X` IS FREE AT THIS PIN — it is `𝒪` pushed forward along the generic point
(2026-07-31.) There is no divisor theory at `a3364fa` — no `𝒪(D)`, no Cartier divisors, no
sheaf of total quotient rings — and three separate audits priced "put this invertible sheaf
inside `𝒦_X`" as new theory on that basis. It is not. For irreducible `X`,
    g  := X.fromSpecStalk (genericPoint X) : Spec X.functionField ⟶ X
    𝒦_X := (Scheme.Modules.pushforward g).obj (modUnit _)
has `Γ(𝒦_X, U) = Γ(𝒪_{Spec K}, g ⁻¹ᵁ U)`, which is `K` for every nonempty `U` (the preimage is
the whole one-point space) and `0` for `∅` — the constant sheaf, exactly. The canonical
`𝒪_X ⟶ 𝒦_X` is the unit of `g^* ⊣ g_*` composed with `modPullbackUnitIso`, i.e. **the same
three-line shape `sectionIdeal` already used**, and multiplication by `a ∈ K` is `pushforward` of
the endomorphism `SheafOfModules.unitHomEquiv` attaches to a global section. The whole
construction elaborated first try. Cost: two imports (`AlgebraicGeometry.FunctionField`,
`AlgebraicGeometry.Stalk`) and about thirty lines.
**And the finding that made obligation (1) of the `g¹₂` route correction cheap: an audit that
bundles two properties into one obligation is usually hiding that one of them is FREE and the
other is ALREADY OWNED.** The obligation read "`sectionIdeal (relSection x)` is INVERTIBLE and is
a subsheaf of `𝒦_X`". The subsheaf half is `kernel.ι` — `sectionIdeal` is *defined* as a kernel,
so it is monic into `𝒪_X` with no hypotheses at all, and `𝒪_X ↪ 𝒦_X` needs only integrality;
neither `IsProper` nor `SmoothOfRelativeDimension 1` enters. The invertible half was already the
named leaf `isInvertibleSheaf_sectionIdeal`, where those two hypotheses are spent. So the only new
content was the `𝒦`-dictionary itself. **Before costing a conjunctive obligation, split it and
price each half separately** — and check whether the second half is already somebody's leaf.
