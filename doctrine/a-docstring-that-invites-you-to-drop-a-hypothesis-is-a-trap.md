## A DOCSTRING THAT INVITES YOU TO DROP A HYPOTHESIS IS A TRAP WITH A WELCOME MAT
(2026-07-31, closing two of the three cases of `exists_ringHom_gamma0GITPresentationOver_of_atlas_aux`
in `X0.lean`.) `exists_rigidifiedModuliData_specF` carried `hℓN : ¬ ℓ ∣ N` under a
Faithfulness note saying it is "**not claimed** to be load-bearing … it is passed in
because it is available at the call site and because whether the development's
`CyclicSubgroupOfOrder` is the Drinfeld notion at `ℓ ∣ N` has not been checked. **A
prover who does not need it should say so and drop it.**"
Dropping it would have closed my leaf in one line. It would also have been the
`one_le_break` failure in a new suit: the two leaves underneath are SORRIES, so widening
them costs nothing at build time and cannot be caught by any test. **A hypothesis on a
sorry leaf is the only thing standing between the leaf and being false; deleting one is
not a simplification, it is an unaudited new claim.**
The check the docstring said had not been run took ten minutes and was not in the
literature — **it was in the file, in the structure definition**. `CyclicSubgroupOfOrder`'s
`geom_cyclic` field demands, at every geometric point, an honest point of order exactly
`N` generating the fibre — i.e. `N` DISTINCT geometric points. `ker F` on a supersingular
curve in characteristic `p` has one. So the structure is the NAIVE notion, the Katz–Mazur
6.6.1 citation attached to it (relative representability and finite flatness, which is a
DRINFELD statement) is not about it at `ℓ ∣ N`, and the invitation was withdrawn in the
docstring rather than accepted.
Generalisable: **when a docstring says a hypothesis is "carried but probably not needed",
treat that as an OPEN QUESTION with a named owner, never as a licence.** Two moves settle
it cheaply, in this order: unfold the DEFINITION the hypothesis is about (not the theorem,
and not the literature), and check what the statement's conclusion asserts about the
degenerate case the hypothesis excludes. Only a written audit of both buys the deletion.
