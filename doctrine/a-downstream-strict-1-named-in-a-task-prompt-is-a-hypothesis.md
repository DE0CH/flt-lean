## A DOWNSTREAM "STRICT −1" NAMED IN A TASK PROMPT IS A HYPOTHESIS — CHECK THE MODULE'S CURRENT SORRY SET

(2026-07-31.) A dispatch prompt said `Modularity/AmpleSheaf.lean` should have
`nonempty_modPullback_modTensor` redirected and `modPullbackTensorComparison`,
`modPullbackTensorComparison_tensorSection` and `isIso_modPullbackTensorComparison`
DELETED, "a strict -1". Every one of those three is **already proven** — `flt-lean-216`
closed them on 2026-07-30 by cutting a smaller leaf under a *different* name,
`modLocW_modPullbackTensorPre`, and by replacing the under-pinned `Nonempty` form with the
pinned `exists_modPullback_modTensor`, which has consumers in `AbelianSchemeIsogeny.lean`
and `X0.lean`.

Performing the prescribed deletion would therefore have removed the proof of a theorem
those consumers rest on, in exchange for a weaker `Nonempty` that cannot replace it — a
build break dressed as a leaf removal. The check is one comment-stripped scan of that
module attributing each `sorry` token to its enclosing declaration; it takes seconds and
does not need the module built. Same principle as the commit-message rule above: a leaf
named as open anywhere is a hypothesis to check, and that includes the prompt you were
given.

