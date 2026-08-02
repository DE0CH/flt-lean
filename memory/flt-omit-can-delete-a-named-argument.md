---
name: flt-omit-can-delete-a-named-argument
description: Adding the linter's suggested `omit` can remove a section variable from the signature entirely, breaking `(k := k)` named arguments at every call site.
metadata:
  type: reference
---

(2026-08-02.) The `unusedSectionVars` linter suggests `omit [Finite k] … in theorem …`.
Obeying it can remove `k` from the declaration's signature ALTOGETHER — not merely an
instance argument — and then every call site written as `foo (k := k) m` fails with

    Invalid argument name `k` for function `foo`
    Hint: Perhaps you meant one of the following parameter names:  • `m`

which reads as a typo in the argument name rather than as a consequence of the `omit` you
just added twenty lines above. Drop the named argument; the declaration is now genuinely
independent of `k`.

Two riders. A knock-on `Variable name `hS` is not explicitly referenced` on a DIFFERENT
declaration usually means a lemma it calls failed to elaborate, so its call became a
`sorry` and the argument went unused — fix the first error, not the warning. And the
standing caution still applies in the other direction: when the linter names an instance
that is load-bearing but syntactically invisible, check the file's falsity audits before
obeying (see the `Module.Finite ℤ_[p] R` case in CLAUDE.md).
