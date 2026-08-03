## `omit [Inst] in` goes ABOVE the doc comment, not between it and the theorem

(2026-07-31, one wasted build round.) The `unusedSectionVars` linter tells you to
write `omit [TopologicalSpace A] in theorem ...`, and the obvious placement — after
the `/-- … -/` docstring, immediately before `theorem` — is a **parse error**:
`unexpected token 'omit'; expected 'lemma'`, reported at the END of the docstring
line, which reads like a problem with the docstring. `omit … in` is a command
combinator and takes the whole declaration, docstring included, so it belongs on
the line ABOVE the `/--`.

Same shape for `open scoped X in` and `set_option … in`. And note the reverse trap:
`open scoped Classical in` on a theorem whose STATEMENT contains a `Finset.filter`
changes which `Decidable` instance the statement elaborates with, so it can silently
make your theorem a different statement from the one its consumers expect. Prefer
the `classical` TACTIC inside the proof.

