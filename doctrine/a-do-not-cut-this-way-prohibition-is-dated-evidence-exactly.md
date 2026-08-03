## A "DO NOT CUT THIS WAY" PROHIBITION IS DATED EVIDENCE, EXACTLY LIKE AN AUDIT
(2026-07-31, `exists_qAdicPolarizedSystem_finiteBase`.) The rule above says a falsity audit is
VOID once the statement is restated. The same is true in the other direction, and it is easier to
miss because the prose sounds permanent: a docstring paragraph headed **"DO NOT CUT THIS THROUGH
`X` — THE RESULTING LEAF WOULD BE FALSE"** is a claim about `X` **as it stood on the day it was
written**, not a standing law. When `X` changes, the prohibition expires with it — and a later
agent who reads the heading and stops has been stopped by history.
The concrete case. `exists_qAdicPolarizedSystem_finiteBase` (finite base field `k`, char `p`)
carried such a paragraph forbidding the obvious cut through `DualStruct`, and the reasoning was
right: `DualStruct.weil_nondegenerate` was asserted at every `(F, x, I, n)` with `(n : R) ∈ I`,
so at `I = (p)`, `n = p` — where `μ_p(k̄)` is trivial and the pairing is constantly `1` — it
concluded `A[p](k̄) = 0`, which an ordinary elliptic curve over `𝔽_p` refutes. `DualStruct` was
UNINHABITED over any positive-characteristic fibre, so the cut really would have produced a false
leaf.
**But the same paragraph named the repair — "gate `weil_nondegenerate` on `(n : F) ≠ 0`, which is
free in characteristic zero".** One binder in `Modularity/AbelianScheme.lean`, one construction
site to fix (the base-change transport, which gets the new hypothesis handed to it and passes it
straight through), and the cut became legal. The prohibition was not a wall; it was a work item
with a wall-shaped heading.
**AND AN EXPIRED PROHIBITION IS A MAGNET — THIS ONE WAS CUT TWICE, A DAY APART, AND NEITHER
AGENT COULD SEE THE OTHER.** The paragraph above was first written as "and nobody had done it".
That was false when written. The gate had ALREADY been made on 2026-07-30 by another agent, and
that agent had gone on to make the whole downstream cut: `main` at 2026-07-31 had none of it,
`merger` had all of it — `weil_nondegenerate` gated (plus `PolarizationStruct.\
weil_hom_nondegenerate`, which the second cut missed), `exists_qAdicPolarizedSystem_finiteBase`
PROVEN, and the residual geometry left as `exists_dualPolarization_finiteBase`. The second run
independently re-derived the gate, re-cut the same seam, wrote a rival predicate
(`IsQAdicPolarizedHom` against `IsQAdicBoundedPolarizationHom`) and a rival residual leaf
(`exists_dualPolarization_of_mult_finiteBase`) with the *same binders and same conclusion*, and
verified all 390 lines green — all of it discardable, because two proofs of one theorem cannot
both be carried.
This is class 5 (the release window) with a specific accelerant, and it is worth naming because
the accelerant is predictable: **a prohibition that names its own repair is the most attractive
target in the file.** It reads as high-value and cheap, so it is exactly what an agent scanning
for tractable work picks — and several will pick it in the same window. The generic advice
("check `merger` before starting") did not fail here so much as it was not run; but the specific
form is stronger and costs one command, so run it whenever a docstring hands you an unblocking
task:
    git show merger:<file> | grep -n '<the leaf the prohibition blocks>'
If that shows the leaf already proven, the prohibition has been spent and the follow-on work is
done. Check `merger` for the CONSEQUENCE, not just for your own target's name — here the target
was still `sorry` on `main` and already proven on `merger`, which is the whole of the trap.
So, four things worth carrying:
1. **Read the prohibition to its end.** This development's docstrings are unusually good about
   naming what would unblock them. A paragraph that says "this is impossible *until* Y" is a task
   description for Y, and Y is often much smaller than the leaf it blocks.
2. **Check the premise against the source before obeying.** `git log`/`grep` the structure or
   declaration the prohibition is about. It costs a minute; the paragraph may predate its own fix.
3. **A false *hypothesis* leaf poisons more than a false conclusion.** The same defect had already
   been audited on the char-0 sibling `exists_dualPolarization_of_mult`, which was recorded FALSE
   AS STATED on 2026-07-30 with `exists_qAdicWeilSystem_of_mult` PROVEN over it — i.e. a proven
   theorem resting on an uninhabitable hypothesis, worth nothing, and *not visible to any
   sorry-count*. Repairing the structure fixed the char-0 half as a side effect of unblocking the
   finite-base one. When you find an audit saying "leaf L is false and the defect is in shared
   structure `X`", the fix belongs in `X` and it pays out at every consumer at once.
4. **When you DO find you were second, decline your own branch — and leave the receipt.** The
   duplicate here was reverted to `main` on its own branch rather than shipped, so the merge
   worker gets an empty Lean payload instead of a two-sided conflict in a 20 000-line file over a
   theorem it already has. The green work stays recoverable at its own sha (`git show 0025e539`),
   named in the revert's commit message. A decline that is committed and points at its own
   history costs nothing and can be reversed; one that is merged costs whoever resolves it.
