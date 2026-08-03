## AN AUDIT OF `Nonempty S` IS VOIDED BY A LATER FIELD ADDED TO `S`
(2026-07-31, `nonempty_hilbertHeckeAlgebra_of_moretBaillySeed`.) The rule that a leaf restated a
second time voids its earlier audit already exists above. This is the same failure through a door
nobody was watching: **the leaf's STATEMENT never changed at all.** Its conclusion is
`Nonempty (HilbertHeckeAlgebra …)`, and the *structure* gained a field.
`KhareWintenberger.lean` carries a CUT ANALYSIS refusing to split that structure into a
PRESENTATION half and an ATTACHMENT half, and its whole argument rests on one sentence —
"`HilbertHeckeAlgebra` contains **no automorphic pin**", so the presentation half goes vacuous.
That was true when written and false a few hours later: the `automorphic` field was added **the
same day**, and `IsQuaternionicEigensystem F E bad (fun w => θ (heckeT₀ w))` is word for word what
the analysis itself names as THE CHECK THAT WOULD MAKE THE SPLIT SAFE — "a predicate pinning
`(T₀, heckeT₀)` to a genuine Hecke algebra WITHOUT mentioning `ρT`" — over the very API it points
at. Two edits, one day, both correct, nobody reconciled them; the verdict "unavailable" then sat
there for three days deterring exactly the work it had itself unblocked.
So: **before believing an atomicity or irreducibility verdict, diff the objects its conclusion
mentions against the version the verdict was written against.** `git log -L` on the structure, or
just read its field list for anything dated after the audit. A verdict about a leaf is only as
current as the DEFINITIONS in its statement, and those have their own owners and their own commits.
Corollary for the other direction, and it is the cheap half: when you ADD a field to a structure,
grep for audits that reason about what the structure does *not* contain. `grep -rn "no automorphic
pin\|contains no\|nothing pins"` cost seconds and would have caught this one.
