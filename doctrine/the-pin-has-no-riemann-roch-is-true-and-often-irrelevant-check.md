## "The pin has no Riemann–Roch" is TRUE and often IRRELEVANT — check for a NORM first

(2026-07-31, flt-lean-133.) Three separate leaves in `ModularCurve/X0.lean` were
priced at "needs `Γ(A,−)` as a functor to `R`-modules together with its rank", i.e. a
Riemann–Roch development. For the pole-order one that price was wrong by a whole
development, and the reason generalises.

**A finite free algebra has a NORM, and the degree of the norm is the invariant you
were about to build by hand.** `WeierstrassCurve.Affine.CoordinateRing` is free of
rank 2 over `R[X]`, so `ord z := (Algebra.norm R[X] z).degree` is defined at this pin
with no new theory, and it IS the pole order along the point at infinity (`ord x = 2`,
`ord y = 3`). Everything a degree function needs is already proven upstream:
`Algebra.norm` is a `MonoidHom` and `Polynomial.degree_mul` is additive over a domain,
so `ord` is additive on products *for free*; `CoordinateRing.degree_norm_smul_basis`
computes it as `max (2 • deg p) (2 • deg q + 3)` in the `{1, Y}` basis, which gives
`max` on sums; and `CoordinateRing.degree_norm_ne_one` is exactly "the value semigroup
is `⟨2,3⟩`". That was enough to prove the linear shape of any SURJECTIVE
`R[W] → R[W']` over a domain — no sheaves, no cohomology, no `𝒪(nO)`.

So before accepting "absent from the pin", ask what STRUCTURE the object already has:
finite free ⟹ norm, trace, characteristic polynomial, discriminant. A `grep` for the
missing *theory name* (`RiemannRoch`, `CartierDivisor`) will always come back empty
and always feels conclusive; a grep for the *invariant you actually need* on the
object you actually have will not.

Two corollaries that cost nothing and were both worth more than the proof:

- **Where an argument BREAKS tells you what the leaf is really about.** The
  domain-only step was "leading terms do not cancel", i.e. `gr R[W] = R[t²,t³]` is a
  domain iff `R` is. So the general-`R` residue is purely NILPOTENT — which promoted
  the file's own `ℚ[ε]/(ε²)` counterexample from a peripheral warning to a statement
  of the whole remaining problem, and re-priced the attack from Riemann–Roch to
  deformation theory.
- **Prove the hypothesis you wish you had.** The leaf took an arbitrary compatible
  `Φ`; two open immersions with equal range plus `ι` being a monomorphism force `Φ`
  to be the canonical equivalence, so surjectivity was free and was the only thing
  the argument consumed. A leaf stated for "an arbitrary `Φ` with `hΦ`" was never a
  generalisation, and nobody had checked.

**THE MCP DOES NOT EXIST FOR A LOOP-SPAWNED AGENT — USE THE OPEN WEB**
(2026-07-31, prover on `exists_neronModelData`). A task prompt instructed
"download BLR *Néron Models* through the Anna's Archive MCP
(`download_annas`)". For an agent started by `flt-loop.py` that route is not
available in either half: `annas-mcp` is not in the agent's tool set, and
`ANNAS_KEY` is unset in the agent's environment — it is exported only in the
shell that launches an interactive Claude Code session — so calling
`annas-mcp.py` by hand fails too. **Task prompts should stop offering it**,
the same way they stopped offering the Lean MCP.
The open web served the whole book in fifteen seconds, and the fleet's network
is unrestricted (`curl https://…` returns 200):
    curl -sL -o blr.pdf \
      "https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf"
    pdftotext -layout blr.pdf blr.txt     # 15469 lines, the WHOLE book, no OCR
Two things that could have stopped this and did not: the `_tc` in that filename
is part of the scan's name and **not** an abbreviation for "table of contents" —
the file is all ~350 pages; and a `WebSearch` summary said the page "doesn't
provide direct access to the specific content", which was a statement about the
snippet the search returned, not about the PDF. Fetch it and look.
So the procedure is: **`WebSearch` for the title plus a distinctive internal
section number, then `curl` the first university-mirror hit, then
`pdftotext -layout`.** Do that before concluding a reference is unobtainable.
Running text and theorem numbering survive extraction cleanly; displayed
formulas do not, so read for the ARGUMENT and restate the mathematics yourself,
exactly as the OCR section below prescribes.
**Copy what you download to `~/sources/`** — outside the repo, since these are
8–16 MB scans — so the next agent does not pay for it again. It currently holds
Katz–Mazur and Bosch–Lütkebohmert–Raynaud, each as `.pdf` plus extracted `.txt`.
