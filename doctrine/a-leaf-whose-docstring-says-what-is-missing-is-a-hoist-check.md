## A LEAF WHOSE DOCSTRING SAYS "WHAT IS MISSING IS A HOIST" — CHECK WHETHER THE HOIST LANDED, AND GREP THE DECLARATION, NOT THE FILE IT NAMES
(2026-08-02, `flt-lean-240`, closing `heckeOp_smul_of_isWeightTwoEigenform` in
`ModularCurve/X0.lean` in about forty minutes, of which six were the proof.)
This tree cuts a particular shape of leaf routinely: the mathematics is
bookkeeping, every ingredient exists, and the only obstruction is that the
ingredients live DOWNSTREAM. The docstring then says so, in terms — here,
*"**WHAT IS MISSING is a HOIST, not a theory.** The `q`-expansion dictionary for
`heckeTransform` lives in `Modularity/Interface.lean`, which is DOWNSTREAM of
this file"* — and names the block, the destination and the reference scan that
justifies the move. Such a docstring is the most actionable thing in the file.
**It is also the one that goes stale fastest, because somebody else performs the
hoist and cannot edit every leaf that was waiting on it.** The move had happened
the day the leaf was cut: the block is now `Modularity/HeckeQExpansion.lean`
(hoisted verbatim on 2026-07-31, same namespace, no consumer edited), `X0.lean`
`public import`s it, and the leaf was a forty-line assembly over
`qCoeff_heckeOp`, `qExpansion_coeff_eq_of_isWeightTwoEigenform`,
`cuspForm_eq_of_forall_qCoeff_eq` and `qCoeffL`.
**The tell, and it is why the ordinary "grep before believing an absence claim"
rule does not fire: the docstring names the file the block USED TO live in.** A
hoist creates a NEW module, so grepping `Interface.lean` — or reasoning about
whether `Interface.lean` is downstream, which it still is — confirms the
docstring and tells you nothing. The check that works is one command and it is
about the DECLARATION:
    grep -rn "def qCoeff\|theorem qExpansion_heckeTransform_coeff" Fermat/ --include=*.lean
    grep -n '^public import' <your file> | grep -i <the concept>
So: **for any leaf whose stated obstruction is a RELOCATION, grep the tree for
the moved declarations and then grep your own import block, before reading
another line of the docstring.** The same applies to "this needs a module
split", "blocked by declaration order", "the machinery is in a file that imports
this one" — all of them name a *layout*, and layout is exactly what another
agent changes without touching your leaf.
Corollary for whoever PERFORMS a hoist: the leaves that were waiting on it are
findable — `grep -rn 'is a HOIST\|WHAT IS MISSING is a HOIST\|hoist out of'` over
`Fermat/` costs seconds — and one sentence on each ("this landed as `X` on
`<date>`") is worth more than the hoist's own docstring. `HeckeQExpansion.lean`'s
header is excellent about what moved and silent about who was waiting.
### The Lean trap that comes with it: TWO `Gamma0GL`s, one `abbrev` and one `def`
`Fermat.Gamma0GL` (`ModularCurve/WeightTwoEigenform.lean`, an `abbrev`) and
`GaloisRepresentation.Modularity.Gamma0GL` (`Modularity/HeckeOperator.lean`, a
`def`) have the same body and are the same term — `WeightTwoEigenform.lean`'s
RIVAL CARRIERS survey machine-checked it, says the equation is `rfl`, and says
**"do not unify them and do not write a bridge lemma"**, while mentioning "one
(harmless) reducibility asymmetry". That asymmetry is exactly where a proof
mixing the two sides breaks, and the message names neither `Gamma0GL`:
    Tactic `rewrite` failed: Did not find an occurrence of the pattern
      GaloisRepresentation.Modularity.qCoeff ?N 0 ?m
    in the target expression
      GaloisRepresentation.Modularity.qCoeff M 0 1 = a 1
    Note: The target expression is not type-correct under the `instances`
    transparency level …
An `abbrev` is reducible and a `def` is not, so a term Lean HAPPILY ELABORATED
(applying a `Modularity`-side function to a `Fermat`-side `CuspForm`) cannot be
`rw`-ed into, because `rw` inserts the replacement at the `Fermat` side's type.
**Do not chase it with `show`/`simp only`/`erw`.** Use a defeq-checking step,
which crosses the gap for free — here `congrArg (qCoeffL M 1) h` followed by
`map_zero` in place of `rw [h, qCoeff_zero_cuspForm]`. The general rule this
file already records ("printed pattern equals printed target ⟹ switch to
`exact`") is the right cure; what is new is the CAUSE, and that it is announced
by the phrase *"not type-correct under the `instances` transparency level"* —
that sentence means a reducibility mismatch, never a wrong lemma.
