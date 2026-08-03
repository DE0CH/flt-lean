## A LAW PROVEN INSIDE AN EXISTENTIAL IS INVISIBLE — RECOVER IT BY UNIQUENESS
(2026-07-31, same file, and this one is worth more than the cut it enabled.)
`exists_abelJacobiPoint` is PROVEN and yields `∃ aj, spec ∧ aj_pre ∧ aj_base`. Every leaf below
it receives `aj` and `spec` as *hypotheses* — and therefore holds neither `aj_pre` (naturality)
nor `aj_base`. Four leaves had been stated that way. The geometry owner could not even say the
Abel–Jacobi image passes through the origin, which is the hypothesis of the SGA3 theorem being
invoked; the identity-component argument was unstartable for a packaging reason.
Nothing was missing mathematically. **The spec DETERMINES `aj` pointwise** (via the file's own
`IsRelPicOf.eq_of_relPicEquiv_tensor`), so any family satisfying it *is* that family and both
laws transport to it. Three short theorems — a uniqueness lemma plus one transport each — put
them in the hands of any consumer, and the hard proof inside `exists_abelJacobiPoint` is not
repeated even once: the new lemmas `obtain` its witness and rewrite along uniqueness.
**Generalisable, and this codebase is full of the pattern.** Whenever a leaf's hypothesis list
is `(f, one clause about f)` and some proven `exists_f` theorem produces `f` with MORE clauses,
ask whether the one clause pins `f` uniquely. If it does, every other clause is free to the leaf,
and withholding them is pure loss. Symptom to grep for: a leaf whose hypothesis is a *choice
function* plus a *specification*, where a sibling `exists_…` theorem in the same file bundles
extra laws about the same object.
Corollary for whoever states such a leaf: **do not hand a consumer a bare `(f, spec)` pair when
you have proven more about `f`.** Hoist the extra laws to standalone theorems quantified over an
arbitrary `f` satisfying the spec, and pass them in. It costs a uniqueness lemma once.
**Unrelated, measured while doing this:** `RelativePicard.lean` takes **11 minutes** under
`lake env lean`, not the ~25 s a task prompt claimed. Time an iteration before planning around it;
at that length the scratch-module rule matters more than usual, and batching every edit into one
verification is not optional.
