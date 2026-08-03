## An import-cone merge can flip a name resolution: export aliases lose to genuine defs

(Release 39, 2026-08-03.) `Deformation.lean`'s `sum_antidiagonal_cons` — proven,
untouched, green on its author's branch — failed after the batch merge with
`Application type mismatch: … expected Set.IsPWO ?m` on every occurrence of
`Finset.antidiagonal`. Nobody edited the lemma. What changed was the FILE'S
IMPORT CONE: the merged module now (transitively) reaches
`Mathlib.Data.Finset.MulAntidiagonal`.

The mechanism, worth knowing in general:

* `Finset.antidiagonal` exists TWICE in the pin. `Algebra/Order/Antidiag/Prod.lean`
  has `class Finset.HasAntidiagonal` with
  `export HasAntidiagonal (antidiagonal mem_antidiagonal)` — an ALIAS, not a
  declaration. `Data/Finset/MulAntidiagonal.lean` has a GENUINE
  `def Finset.antidiagonal (hs : s.IsPWO) (ht : t.IsPWO) (a : α)` (the
  `to_additive` of `mulAntidiagonal`; the old `addAntidiagonal` names were
  deprecated into it 2026-06-08).
* A genuine declaration beats an export alias at name resolution. So the same
  source text means the `HasAntidiagonal` operation in a file that does not
  import `MulAntidiagonal`, and the `IsPWO` one in a file that does.
* A merge that only ENLARGES an import block (here: `Deformation.lean` gaining
  `public import …HilbertModularity` and the ContCohomology modules) can
  therefore break proofs in UNTOUCHED regions of the file, with error messages
  pointing at code no branch edited.

Repair: fully qualify (`Finset.HasAntidiagonal.antidiagonal`,
`Finset.HasAntidiagonal.mem_antidiagonal`) at the affected sites — that names
the same constant mathlib's own `coeff_mul` lemmas elaborate to, so rewrites
still match.

Detector, when a merged file errors in a region `git diff` says nobody
touched: suspect ambient-resolution drift, not the code. Check whether the
erroring identifier has BOTH an export alias and a genuine declaration in the
pin (`grep -rn "export .*(<name>" ` and `grep -rn "def <name>\|alias .*<name>"`
over `.lake/packages/mathlib`), then compare the file's import block before and
after the merge.
