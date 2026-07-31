---
name: flt-verify-against-last-green-release-oleans
description: When your target lives only on `merger` and `merger`'s upstream module is red, verify with bare `lean` against `~/.flt-release-lake`'s oleans — and prove the shim sound by diffing the API you use between `main` and your tree.
metadata:
  type: project
---

(2026-07-31, `flt-lean-115`, on `exists_x1IntegralSmoothProperModel`.) Release 27 was
NOT published: `main` stayed at the last green release and `merger` carried
`ModularCurve/X0.lean` with ~193 inherited errors (`tools/merge/RELEASE-27-HANDOVER.md`).
The target existed only on `merger`, so merging it was correct — and it made
`lake build Fermat.FLT.ModularCurve.X1` impossible, because `X1` imports `X0`.

**The shim is the answer, and repairing the red module to unblock yourself is not.**

    cp -rs ~/.flt-release-lake/build/lib /tmp/relean-N/
    LP=$(lake env printenv LEAN_PATH); LSP=$(lake env printenv LEAN_SRC_PATH)
    LEAN_PATH="/tmp/relean-N/lib/lean:$LP" LEAN_SRC_PATH="$LSP" lean Fermat/Scratch.lean

The farm holds the LAST GREEN RELEASE's artifacts, so the red module is replaced by its
green predecessor. ~1 min per round; 440 lines verified first try.

**Why:** a green scratch means nothing unless every name you use is present AND unchanged
at the snapshot's sha. Check it mechanically (`git show main:<file>` and diff the
declaration texts). That check also tells you what you may NOT use — here
`exists_unit_natCast_of_isReductionBase` is merger-only, so the new leaf was stated over
`IsReductionBase` rather than over the Katz–Mazur unit proviso, with the improvement
named in its docstring instead of taken.

**How to apply:** extract the scratch from the real file BY LINE RANGE after the edit is
in place, so the verified text and the committed text are the same characters. Say in
`to_merger` that `lake build` of the module was impossible and name the blocker.

Related: [[flt-see-the-merge-before-the-merger]], [[flt-loop-spawn-liveness-race]].
