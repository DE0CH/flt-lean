## A REDUNDANT PRINTED COLUMN IS THE ONLY DRIFT GUARD A COMMENT CAN HAVE

(2026-07-31, same run.) `x0HeckeCharpolyTable`'s docstring prints a human-readable table beside
the `def`, including three columns — `Tr`, `ℓ+1−Tr`, `det((ℓ+1)−T)` — that are NOT stored and are
computed from the polynomial by proven lemmas. Its `N = 75` row printed `X⁵ − 9X²` while the
banked list `[0,0,0,-9,0,1]` is `X⁵ − 9X³`.

The `def` was right and the prose was wrong, and the redundancy is what proves it **without any
external tool**: the same row prints `det = 28160`, and `8⁵ − 9·8³ = 28160` while
`8⁵ − 9·8² = 32192`. Two printed columns that must agree, disagreeing.

The general point: a `decide`-backed drift guard (`x0Genus_eq_of_mem_x0HeckeCharpolyTable`,
`exists_charpolyRow_of_x0WitnessTable`) breaks the BUILD when data drifts, which is why this
development uses them. **A docstring table is a comment; nothing checks it, and it is read far more
often than the `def`.** So when banking numerical data, print the derived columns too — they cost
nothing and they are the only thing standing between a typo and a prover chasing the wrong
polynomial. And when reading such a table, cross-check a derived column before trusting a row; a
CAS run is confirmation, not the first line of defence.

