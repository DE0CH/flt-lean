## An AUDIT'S "this is the blocker" can name a hypothesis the proof never reads
(2026-07-31, `flt-lean-324`.) `IsogenyTrace.lean`'s leaf
`exists_weilPairing_torsionRep_adjoint` carried a fourth-pass audit, re-verified
twice, saying the divisor-theoretic Weil pairing in this tree was
characteristic-`p`-only because two Stage-B declarations
(`exists_generic_pDivision_offset`, `exists_millerRatio_eval_translationChar`)
take `{F₁ F₂ : Subfield F}` with `(F₁ : Set F).Finite`, and a finite subfield
containing the curve's coefficients exists only in characteristic `p`. The audit
described that boundary as "sharp" and priced the char-0 route off it.
**Every one of those finiteness hypotheses was dead.** In leaf 1 they were already
`_`-bound in the source — `_hF₁fin`, `_hF₂fin` — i.e. the file itself said the proof
never looks at them, in the signature, for months. In leaf 3 the `unusedVariables`
linter named eight unused binders (`hF₁fin`, `hF₂fin`, `hF₁₂`, `hbad`, `hySF₂`,
`hxSF₁`, `hyPSF₂`, `hxPSF₁`) on every green build of the module.
So the first check, before believing any audit's account of what makes a leaf
expensive, costs one grep of a build log you already have:
    grep 'is not explicitly referenced' /tmp/build.log
Lean's linter reports theorem BINDERS, not just tactic-block locals. A hypothesis
it flags is not load-bearing, whatever the docstring says about it.
**The second half is what the linter cannot give you, and it is where the win was.**
A hypothesis that *is* used may still be used only as a *device*. Grep the proof body
for the name, find the local it feeds, and count that local's applications. Here the
whole field hierarchy — coefficient memberships, `exists_pointSubgroup_of_subfield`,
`hbad`, six memberships — fed one local `hkey : ∀ t ∈ G, S ⊖ R ≠ t`, applied at
exactly four values of `t`. The subfield was an *avoidance* device: "pick a point
outside a small bad set", implemented in characteristic `p` by enumerating a large
enough finite field. Restated over those four inequations, both declarations became
characteristic-free, and characteristic zero turned out to be the EASY side — the
base is infinite, so the avoidance is direct.
* **"Needs a finite field" is very often "needs to avoid finitely many things".**
  Those are opposite in difficulty over an infinite base. When a leaf's stated
  obstruction is a finiteness/enumeration hypothesis, check which one it is before
  costing the work.
* **Generalise by keeping the old statement as a WRAPPER.** Move the proof to the
  weaker-hypothesis version, then re-derive the original from it in a few lines.
  The change is then strictly additive: no consumer's call site moves, and a green
  build cannot regress. Both Stage-B leaves were generalised this way with the 15k-line
  `WeilPairing.lean` caller untouched.
