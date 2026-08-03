## A LEAF'S "THIS IS THE WHOLE CONTENT" PARAGRAPH CAN NAME A LEAF THAT IS ALREADY IN THE SAME FILE — GREP THE PROSE, NOT THE IDENTIFIERS
(2026-08-02, `flt-lean-35`, `Modularity/TateModule.lean`.)  This file already
records that two leaves can carry one theorem under names sharing no identifier,
and prescribes `tools/merge/dupstmt.py` for the case where the two STATEMENTS
match up to alpha-renaming.  There is a commoner and completely invisible
variant: the two statements are genuinely different theorems, and one of them is
provable from the other, so what is duplicated is not the statement but the
**obstruction**.  Nothing mechanical sees it.
`exists_ne_zero_mem_torsion_isMaximal_finiteBase` (a nonzero abelian variety with
`𝒪_D`-action has nonzero `I`-torsion) carried a careful audit ending:
> What rules that out is the `ℓ`-INDEPENDENCE of the local ranks, i.e. genuine
> Tate-module theory, **and that is the whole content of this leaf**.  A prover
> who has proved faithfulness has not started.
Every word true.  `finrank_mulByElt_of_relativeDimension` — the theorem of the
cube with the relative dimension free, a `sorry` leaf **20 000 lines above in the
same file** — says the same thing in the same words:
> a module over a product of fields need not be free — the exponents `dᵢ` are the
> local ranks, and their equality is precisely what the Galois argument supplies
> and what a count at one `λ` cannot see.
Two leaves, one obstruction.  The target is now PROVEN over that leaf plus
elementary glue: **frontier −1, no new leaf, and the `ℓ`-independence is stated
exactly once.**
**THE CHECK IS ONE `grep` AND IT IS ON THE PROSE.**  Identifier scans, statement
scans and `own.py` are all silent here by construction — the two statements share
no name, no type and no conclusion.  What matches is the docstring:
    grep -n "local ranks" Fermat/FLT/Modularity/TateModule.lean   # finds both, instantly
So when a leaf's docstring names its obstruction in words — "`ℓ`-independence",
"the freeness of a Tate module", "Riemann–Roch in degree 1", "positivity of the
Rosati involution" — grep the file's OTHER leaf docstrings for that phrase before
costing any work.  This development writes those phrases down precisely so they
can be matched; almost nobody matches them.
### The three moves that made the glue elementary, each reusable
* **A "the object is nonzero" hypothesis substitutes for "the dimension is
  positive" via FINITE + DIVISIBLE.**  The leaf's `hnz` had to exclude relative
  dimension `0`, and the classical route (finite étale + connected + a section ⟹
  degree one) needs the structure theory of étale algebras.  It is not needed:
  a rel-dim-`0` abelian scheme has a FINITE geometric fibre, that fibre is
  DIVISIBLE by every `M ≠ 0` (`exists_nsmul_eq_geomFibrePt`, true in every
  characteristic), and a finite divisible abelian group is trivial.  Three lines.
* **`card_fibrePt_eq_of_finrank_eq` gives `Nat.card = n`, which is NOT finiteness
  — `Nat.card` of an infinite type is `0`.**  What upgrades it is
  `Scheme.Hom.one_le_finrank_map f x : 1 ≤ f.finrank (f x)`, which needs only a
  POINT of the source and no surjectivity; the zero section supplies one.  Then
  `Nat.card ≠ 0` gives `Finite`.  Reach for `one_le_finrank_map`, not
  `one_le_finrank_iff_surjective`, whenever you have a section.
* **A specialisation is droppable exactly when the general lemma was already
  extracted with the specialised quantity as a PARAMETER.**  Dropping `hdim'` and
  `[IsTotallyReal D]` from the `#A[(a)]` count cost nothing, because
  `card_torsion_span_singleton_of_finrank_mulByElt` already takes the DEGREE as an
  argument — its own refactor note says it was extracted "so that it can be used in
  BOTH directions".  When a leaf's hypothesis looks unavoidable, check whether the
  theorem beneath it has already been split that way; if it has, the hypothesis is
  only in the wrapper.
### And the standing lesson fired again: I wrote a mathlib-facing helper that already existed
`locallyQuasiFinite_of_formallyUnramified` (étale ⟹ locally quasi-finite, the
piece genuinely absent from mathlib's `QuasiFinite.lean`) was written from scratch
here, verified, and only then found — PROVEN, character for character the same
statement — in `Modularity/AbelianSchemeIsogeny.lean`, which the target module
`public import`s.  The grep that finds it is on the CONCLUSION
(`grep -rn "LocallyQuasiFinite" --include=*.lean Fermat/`) and takes one second.
Run it before writing any `Fermat/FLT/Mathlib/`-shaped lemma, and run it on
`Fermat/` and not only on the pin.
