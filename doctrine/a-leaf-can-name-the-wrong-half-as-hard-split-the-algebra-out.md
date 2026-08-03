## A LEAF CAN NAME THE WRONG HALF AS HARD — split the algebra out before building the theory
(2026-07-31, `ProperPushforward.lean`.) That file's single leaf,
`self_mem_smul_adjoin_self_of_appTop_fiberι_eq_zero`, carried six audit blocks — (A)–(D) on
`finiteType_appTop_of_isProper`, (E)–(H) on the leaf — each with an explicit witness, all
correct, all agreeing that closing it is a THEORY BUILD (Grothendieck coherence, absent from
the pin) and that every proposed shortcut is dead. Every one of those conclusions still
stands. And the leaf still closed, because the audits were about the GEOMETRY and the leaf as
stated bundled the geometry with a commutative-algebra bridge that was fully provable at the
pin in ~110 lines.
**The tell was in the file and is worth looking for generally: a statement of the honest
classical input sitting BELOW the leaf and proven CIRCULARLY from it.** Here it was
`exists_finiteFree_ker_linearEquiv_appTop_of_isIso_appTop_fiber` (Mumford's complex in degree
`0`), discharged by "once the leaf is known, `A ≅ R`, so take `R¹ ⟶ R⁰` with `d = 0`". A
declaration whose proof is *"assume the leaf, now the witness is trivial"* is not content —
it is the file telling you its dependency order is inverted. Hoist it above the leaf, make
IT the leaf, and prove the old leaf from it. The two are then provably equivalent, so no
audit is voided and none of the recorded witnesses is lost.
**The technique that made the bridge provable, and it generalises.** The natural hypothesis
on a two-term complex is `Module.Flat R (range d)` — that is what a Tor computation gives
`ker d ∩ 𝔪·C₀ ≤ 𝔪·ker d` from. But the Nakayama step ALSO needs `Module.Finite R (ker d)`,
and in this file the only source of that was downstream of the leaf, so the flat form was
unusable exactly where it was wanted. **Ask for `Module.Projective R (range d)` instead**: it
splits `0 ⟶ ker d ⟶ C₀ ⟶ range d ⟶ 0`, and the retraction `r : C₀ ⟶ ker d` gives BOTH facts
in one line each (`ker d` is a quotient of the finite `C₀`; `r` carries `𝔪·C₀` into
`𝔪·ker d` and fixes `ker d`). The two hypotheses agree in the intended application — a
finitely presented flat module is projective — so nothing is given up. General form: **when a
flatness hypothesis is unusable because the finiteness its Tor argument needs is the very
conclusion, ask for the SPLIT rather than the Tor-vanishing.**
**A third thing, about tensor products.** The dévissage those complexes are for (`H⁰(J) :=
ker(d ⊗ J)`, left exact by flatness of the terms) needs no tensor product to state: flatness
of `C₀` identifies `ker(d ⊗ J)` with the honest submodule `ker d ∩ J·C₀`. Whenever a route is
written with `⊗` over a filtration of ideals, check whether flatness lets it be written with
`Submodule.inf` and `Submodule.smul` first — the Lean cost is an order of magnitude lower.

