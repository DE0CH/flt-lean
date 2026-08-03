## A PROOF ROUTE THAT DIES IN ONE CHARACTERISTIC: SPLIT THE LEAF, DO NOT WEAKEN THE PARENT

(2026-07-31, `flt-lean-313`, `exists_diffCharScalar_polyData`.)

The pullback-factor leaf of `DifferentialCharacter.lean` is proved by a valuation-and-degree
count on `ℙ¹` run against `Ψ_{W′}(x) = γ²Ψ_W`. That identity is FREE — a `linear_combination`
of the leaf's own two hypotheses, machine-checked and quoted in the docstring — and in
characteristic `2` it is **VACUOUS**: `Ψ = 4X³ + b₂X² + 2b₄X + b₆ = (a₁X + a₃)²` is a square,
`4 = 0`, and the identity collapses to the OTHER hypothesis squared. So the count proves the
statement everywhere except at one prime, where it proves nothing — and the statement is
still TRUE there (it is *AEC* III.5.2, which is characteristic-free).

**A derived identity can be an identity and still be empty.** Nothing about its derivation
warns you: it type-checks, `ring` closes it, and it is genuinely a theorem. Before building a
count on one, instantiate it in the degenerate characteristic and check it still separates
the things it is supposed to separate.

Two ways out, and they are not equally good:

* add `(2 : F) ≠ 0` to the parent — cheap on paper here, since the only consumer
  (`MazurTorsion.lean`) is over `AlgebraicClosure ℚ`. But it moves an INTERFACE, and an
  interface change together with its call sites is exactly what the seventh invisibility
  class above says a merge can split across the conflict boundary;
* **keep the parent's signature and `by_cases` on the characteristic, with the bad branch a
  NEW NAMED LEAF.** Nothing upstream moves, no consumer in any worktree has to be found and
  edited, and the residual is stated at exactly the generality where it is hard.

The second is right by default. The cost is one declaration; a leaf is much cheaper than an
interface.

And go one further while the algebra is in front of you: in the char-`2` branch `hone`
collapses (its `2DB` term dies) and `hcurve`'s two middle terms fold into it, which removes
`E` and `Cx` from the CONCLUSION and takes the residual from five polynomials to four. That
reduction is REVERSIBLE and cost ten lines, so what a successor is dispatched at is the small
statement. A leaf handed on in its raw form makes the next agent re-derive the collapse
before starting — and there is no reason for two agents to do that.

### `omit [X] in` goes BEFORE the doc comment

`omit [DecidableEq F] in` placed between a `/-- … -/` and its `theorem` is a syntax error —
`unexpected token 'omit'; expected 'lemma'`, reported at the END of the doc comment's last
line, which reads like a problem with the comment. A doc comment must be adjacent to its
declaration. Put the `omit` above the doc comment; `DifferentialCharacter.lean` already does
this in twenty places, so copy a neighbour rather than guessing.

