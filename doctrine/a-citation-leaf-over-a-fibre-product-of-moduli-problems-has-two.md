## A CITATION LEAF OVER A FIBRE PRODUCT OF MODULI PROBLEMS HAS TWO FACTORISATIONS — a rejected cut in one order says NOTHING about the other
(2026-07-31, `flt-lean-281`, on `exists_isAffine_gamma1RigidifiedModuliScheme` in
`ModularCurve/X1.lean`.)
The node asked for the rigidified moduli scheme `𝔐([Γ₁(N)], [Γ(n)])` — one object
sitting over TWO moduli problems. Its docstring recorded, correctly, that the obvious
decomposition had been **considered and rejected on 2026-07-30**: cut it as
"`𝔐([Γ(n)])_K` is affine" plus "the forgetful morphism is affine", and you get two
citations *plus* a new definition, because the file has no `𝔐([Γ(n)])` and no
`Gamma nDatum` to state either half about. That verdict is right about that order.
**It is silent about the other order, and the other order costs no new vocabulary.**
Put `[Γ₁(N)]` at the BOTTOM: `Gamma1Datum` and `IsBaseChangeOfGamma1` have been in the
file since the beginning, so the bottom leaf is stated in existing words, and the top
leaf ("full level `n` is relatively representable, affine over the base") is stated with
the existing `AbelianFullLevelStructure`. The new `structure Gamma1ModuliScheme` is a
*packaging* of three existing fields and one existing `∃!`, not a new notion. The
assembly is ~20 lines (`isAffine_of_isAffineHom` for the affineness, and the two `∃!`s
compose through `IsBaseChangeOfGamma1.comp`), and it verified in **10 seconds** in a
scratch module.
**So when a docstring says a tower cut was rejected, check WHICH ORDER was priced.** A
fibre product `A ×_C B` factors two ways, the two residues are different theorems from
different chapters, and this development's vocabulary is almost never symmetric between
them — one order will be expressible in words the file already has and the other will
not.
Three things the re-cut bought, and they are the terms on which a `1 -> 2` trade should
be argued, since the count alone says the cycle went backwards:
* **the bottom leaf is a STRICTLY SMALLER citation.** Katz–Mazur (4.10) + Corollary
  4.7.1 give `[Γ₁(N)]` alone, representable by a *smooth affine curve* for `N ≥ 4` —
  so (4.7.2), (5.1.1), (6.6.2) and the 8.1.1 affineness parenthesis all drop out, the
  last because affineness is part of 4.7.1's own conclusion;
* **the top leaf stopped being a citation.** Section `IsomTorsorCoverX1` in the same
  file (written 2026-07-30) already builds the representing object — the clopen locus in
  `E[n] ×_T E[n]` where the tautological sections are independent — and `IsAffineHom` is
  free from it being CLOSED in a finite `T`-scheme. What is missing is the universal
  property, i.e. Lean, not literature;
* **a hypothesis stopped being decoration.** `_hN : 4 ≤ N` is genuinely not load-bearing
  for the merged statement (the `n ≥ 3` level structure rigidifies whatever `N` is), and
  it IS load-bearing for the bottom leaf: at `N = 3`, `j = 0`, the order-`3` automorphism
  fixes a point of exact order `3`, so `[Γ₁(3)]` is not rigid and the bottom structure is
  uninhabited. A binder that is inert in a merged node can be the whole content of one of
  its factors — check before underscoring, and re-check when you cut.
### The recon that decided it, and the numbers, so nobody re-derives them
* **`~/cs/FLT` has NOTHING here.** `grep -rn 'moduli'` over `~/cs/FLT/FLT` returns two
  prose mentions inside `KnownIn1980s/EllipticCurves/Flat.lean`; `IsAffine` returns
  **zero** hits in the whole project; `representable` returns only Schlessinger
  corepresentability in `Deformations/Representable.lean`. No `(Ell)`, no level
  structure, no Weierstrass family over a general base. Pin drift never became a
  question.
* **Katz–Mazur is already downloaded**, at `~/flt-lean/sources/katzmazur1985ame.txt`
  (OCR, 665 KB) — do NOT spend an Anna's Archive quota slot on it. 4.7.1 is at line
  4637, 4.7.2 at 4662, the `N ≥ 4` sentence for `[Γ₁(N)]` at 4790, 5.1.1 at 6360,
  6.6.2 at 6754, 8.1.1 at 8705.
* **4.7.1 rests on ~110 book pages** — its own proof is four lines and every line is a
  forward reference (4.7.0, the free quotients, the explicit equations 2.2.9/2.2.11,
  rigidity 2.7.2, relative representability 3.7.1), i.e. all of Ch. 1–4.
* **Size, calibrated against this repository rather than guessed:**
  `ModularCurve/EllipticScheme.lean` is **13 629 lines** to give ONE Weierstrass curve,
  over the FIXED base `Spec ℚ`, a projective model and an `AbelianSchemeStruct`
  (`ProjCoords` is declared for `E : WeierstrassCurve ℚ`, and
  `abelianSchemeStruct_of_projGroupLaw` is the only construction of an
  `AbelianSchemeStruct` from a Weierstrass equation in the tree). A universal family
  over a moduli scheme needs that at a GENERAL base ring. Honest estimate for the whole
  node: **400–800 declarations, 15 000–30 000 lines.** Not a single run.
