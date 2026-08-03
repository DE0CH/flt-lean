## ADDING A CONJUNCT MID-CHAIN BREAKS EVERY `obtain` ON IT, INCLUDING ONE IN ANOTHER FILE
(Same task.) Threading a new conjunct through a chain of `∃ x, A ∧ B` wrappers
changes the ARITY of every anonymous-constructor pattern that destructures them.
`obtain ⟨c, hinj, hc⟩` against `∃ c, Inj c ∧ (∀ d, …) ∧ (new)` still elaborates —
it binds `hc` to the CONJUNCTION — and then fails much later, at the first use,
as **`Function expected at hc`**. That error names the binder, not the theorem
whose statement moved, so it reads like a broken proof.
Two things follow:
* **Find the call sites by grepping the THEOREM NAME applied, not the binder**,
  and do it across the whole tree before building: here one of the four was in
  `FreyCurve/MazurTorsion.lean`, i.e. the class-7 interface split with the two
  halves in two files. Cost of missing it: one full build of a 119 000-line
  module.
* **Append the new conjunct LAST at top level**, never in the middle: then every
  existing pattern needs exactly one extra `-` and no reordering, and the diff at
  each call site is one character plus a comment saying which release added it.
