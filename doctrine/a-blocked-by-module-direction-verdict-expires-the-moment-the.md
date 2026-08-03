## A "BLOCKED BY MODULE DIRECTION" VERDICT EXPIRES THE MOMENT THE HOIST LANDS — RE-GREP THE BLOCKER'S IMPORT BLOCK
(2026-08-02, `flt-lean-97`, on `exists_frickeSlash_eq_smul_of_isNewEigenformAt` in
`ModularCurve/X0.lean`.)  CLAUDE.md already has a section on this leaf —
*A LEAF BLOCKED BY MODULE DIRECTION IS STILL FULLY VERIFIABLE* — which correctly says
that when the theory a leaf needs sits in a module that IMPORTS the leaf's file, you
cannot land the proof, and prescribes banking a compiled block instead.  It is right,
and it has an expiry date that nothing writes down.
**The hoist it recommended had LANDED, and the leaf had been provable for a release.**
`Modularity/HeckeAtkinLehner.lean` (7 827 lines, hoisted out of `Interface.lean`)
imports only `HeckeOperator` and `HeckeQExpansion`; `HeckeOperator.lean` has NO project
imports at all and `HeckeQExpansion.lean` imports only `HeckeOperator`.  Neither reaches
`X0.lean`, so the edge `X0 → HeckeAtkinLehner` creates no cycle — and `X0.lean` already
imported both of the other two.  The leaf's own docstring still said, in bold, that
*"none of the declarations above may be named here"*, and every agent sent at it could
only re-derive that.
**The check is ONE command and it is not the one the docstring tells you to run.**  The
docstring's own refuting check was *"find an import path from `HeckeOperator.lean`'s
neighbourhood back into `ModularCurve/X0.lean`"* — an absence, which is expensive to
establish and easy to believe.  The cheap positive form is to read the BLOCKER'S OWN
import block:
    grep -n '^public import Fermat\|^import Fermat' <the module holding the theory>
If it does not mention your file, the blockage is gone.  Seconds, no build.  Then
confirm with `python3 tools/merge/cyclecheck.py`, which scans the whole tree and is the
instrument that settles it.
**AND THE BANKED BLOCK PAID OFF EXACTLY AS DESIGNED.**  `HANDOFF-fricke-multiplicity-one.md`
held 557 compiled lines written against `Interface.lean` on 2026-07-31.  Re-pointed at
`HeckeAtkinLehner.lean` it compiled **unchanged, first try, in 9.5 s**, `EXIT=0`, with
exactly its one named `sorry`.  So the handoff technique is validated end to end: bank
the block, and the leaf closes in an afternoon whenever the hoist lands.  **When you
write such a handoff, say WHICH GREP RETIRES IT** — this one did not, which is why it
sat unclaimed.
**Land it in a NEW MODULE between the two, not in either of them.**  The block needs the
Fricke vocabulary (`frickeSlash`, `frickeMatrix`, `Fermat.IsWeightTwoEigenform` — all in
`ModularCurve/WeightTwoEigenform.lean`, which has NO project imports) and the
Atkin–Lehner theory.  So `ModularCurve/FrickeMultiplicityOne.lean` importing exactly
those two carries 530 of the 557 lines, conflicts with nobody, and leaves `X0.lean` (the
most-edited file in the tree) needing one import line and fifteen lines of assembly,
while `HeckeAtkinLehner.lean` — concurrently being de-duplicated against
`HeckeQExpansion.lean` — is not touched at all.  **Before assuming your block must go in
the giant file, grep where its vocabulary is actually DECLARED**; here only
`IsNewEigenformAt` was in `X0.lean`, and it is used by exactly two declarations.
Two mechanical notes, each of which cost a round:
* **Do not re-namespace a verified block.**  Moving it from
  `namespace GaloisRepresentation.Modularity` into `namespace Fermat` broke it
  immediately: bare `Gamma0GL` then resolves to `Fermat.Gamma0GL` rather than
  `Modularity.Gamma0GL`, the two are DEFEQ BUT NOT SYNTACTIC, and `rw` chains leave
  goals that print as `X = X` and are not closed.  (`IsWeightTwoEigenform` clashes the
  same way, with a different arity, giving `type expected, got`.)  Keep the block in the
  namespace it was verified in and cross the boundary ONCE, in the final assembly, where
  a term-mode application unifies the two carriers at default transparency —
  `CuspForm (Fermat.Gamma0GL M) 2 = CuspForm (Modularity.Gamma0GL M) 2` is `rfl`.
* **`lake env lean` cannot see a module you have just written** — it consumes oleans, so
  a scratch importing your new file dies with `object file … does not exist` until you
  `lake build` it once.  That reads like a broken `.lake` and is not.
**Report the count honestly: this was `−1 +1`.**  `flt-frontier` 382 → 382, `X0.lean`
101 → 101, one name out (`exists_frickeSlash_eq_smul_of_isNewEigenformAt`, now PROVEN)
and one in (`eigensystem_minimal_of_isNewEigenformAt`, Atkin–Lehner Thm 1).  What
changed is that a leaf which was a MODULE-DIRECTION ARTEFACT became a leaf that is real
mathematics, and that ~530 lines of Atkin–Lehner plumbing plus the whole coefficient
half of the carrier bridge are now proven and `#print axioms`-clean
(`[propext, Classical.choice, Quot.sound]`).
