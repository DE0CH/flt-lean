## A `∀`-SHAPED LEAF DEFENDED BY "THE OBJECT IS UNIQUE" IS TWO LEAVES PRETENDING TO BE ONE APIECE

(2026-07-31, `X0.lean`, `flt-lean-400`.) A recurring shape in this development: a
universal-property structure `D` (fine moduli, initial object, coarse space), one leaf
asserting `Nonempty D`, and a SECOND leaf asserting `∀ R : D, P R.M` for some
iso-invariant `P`. The second leaf's docstring always defends the `∀` the same way —
"`universal` is a fine moduli property, so any two inhabitants are related by a unique
isomorphism, hence *some* inhabitant satisfies `P` iff *every* one does" — and then
does **not prove it**, because the leaf is sorried anyway.

**That unproven sentence is the whole cut.** Prove it — it is elementary and carries no
citation — and the two leaves collapse into one `∃ R : D, P R.M`, from which both follow.
Here that took ~55 lines and turned `exists_rigidifiedModuliScheme_specF` +
`isAffine_of_rigidifiedModuliScheme_specF` into theorems over a single fused leaf, with
**no signature and no consumer changed** — only the two bodies moved.

Three things make this worth looking for rather than waiting for:

- **The parallelism the cut buys is usually illusory.** Both halves here needed `Y(n)`
  constructed; whoever built it got the second half in the same sentence of Katz–Mazur.
  Splitting them made two agents build the same object.
- **The rigidity proof is cheap when the base-change relation is a CATEGORY.** The
  argument is: feed each inhabitant's universal family to the other's `universal`, then
  observe that `m' ≫ m` and `𝟙` both solve the *same* `∃!`. That needs exactly a `refl`
  and a `comp` for the relation — in `X0.lean` those are `IsBaseChangeOf.refl` and
  `IsBaseChangeOf.comp`, both already PROVEN. Check for them before assuming the argument
  is expensive.
- **Fusing STRENGTHENS the statement, so re-audit faithfulness.** A `∀`-shaped leaf is
  *vacuously true* when `D` is uninhabited; the fused `∃`-shaped one is false there. In
  this instance that made `hn : 3 ≤ n` load-bearing for TRUTH rather than merely for the
  citation. Say so in the new docstring — an inherited faithfulness audit does not survive
  a restatement (see the two-correct-repairs section above).

The counter-consideration, and it is real: this UNDOES a deliberate cut, so it is only a
win if you actually pay the rigidity proof. Weakening `∀ R, P R.M` to `∃ R, P R.M`
*without* proving rigidity is a strict loss, and is what the leaf docstrings were warning
against. Pay it or leave the cut alone.

**Ordering can block it, and that is worth checking FIRST.** The identical fusion applies
to the `ℚ` twins in the same file and was not done, because `IsBaseChangeOf.refl` is
declared ~600 lines BELOW them: the rigidity lemma cannot be stated where it would be
consumed. Hoisting 34k-line-file material is its own merge hazard (see class seven), so
that one was queued rather than attempted.

