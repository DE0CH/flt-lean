## A CUT-ANALYSIS SAYING A ROUTE "CANNOT BE AVOIDED" IS A HYPOTHESIS ABOUT A PROOF

(Same run, and the reason the leaf fell at all.) `mem_gp_one_of_dvd_smul_unif_sub` carried a
careful, signed analysis concluding it "CANNOT BE AVOIDED" without the monogenicity
`𝒪_L = 𝒪_0[unif]` plus Hensel: `δ_x(σ) := (σ•x − x)/unif mod 𝔪` is a DERIVATION in `x`, so it is
"determined by its value on a ring GENERATOR, and nothing weaker". The analysis was right about the
derivation and right about the two substitute routes it examined (both re-verified dead). It was
wrong about the conclusion, and the counter-proof is forty lines.

The move that dissolves it is worth naming, because it generalises: **attack a `∀ x` by CASES on
the element, not by a normal form for it.** Here `mem_gp`'s quantifier splits as unit / non-unit;
non-units are `unif · y` by `unif_spec`, and a UNIT is soft because `R^×` is, modulo `𝔪`, torsion of
order prime to `p` — the residue field of a finite level is FINITE. A derivation is determined on a
generating set, but the generating set may be `{unif} ∪ R^×` rather than `{unif}`, and then no
generator theory is needed at all.

Two agents a day apart found exactly this proof, both against the docstring's own "impossible".
So the standing rule: **a cut-analysis records which routes were tried, and that is all it records.**
Read it for the dead ends it certifies — those are real and save time — and re-derive the negative
conclusion yourself. The same applies to any "needs new theory" or "ATOMIC" verdict in this tree.

