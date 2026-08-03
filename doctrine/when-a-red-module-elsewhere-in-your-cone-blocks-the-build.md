## WHEN A RED MODULE ELSEWHERE IN YOUR CONE BLOCKS THE BUILD, ELABORATE AGAINST THE **PRISTINE** RELEASE SNAPSHOT
(2026-07-31, `flt-lean-117`, on `HilbertModularity.lean`.) The scratch-module and
`LEAN_PATH`-farm tricks above are written for one situation — `lake build` has deleted
the olean of the very file you are editing. There is a second, and under a
non-publishing release it is the commoner one: **your file is fine and some unrelated
module in its import cone is RED.** `ModularCurve/X0.lean` has not built since release
25; it is in the cone of 8 modules including this one; and
`tools/merge/RELEASE-27-HANDOVER.md` hands its repair to a dedicated owner as a
multi-hour job. So `lake build <your module>` cannot terminate green for anybody
downstream of X0, however correct their own work is.
The move is **not** to patch the missing olean into your own `.lake`. That produces
exactly the inconsistent-olean state CLAUDE.md already warns about — here it would have
mixed merger-era oleans for the 46 changed cone modules with release-era oleans for the
7 that sit under X0 and therefore never got rebuilt, and every diagnostic from that mix
is untrustworthy. Use a **pristine, internally consistent** set instead:
    rm -rf /tmp/relean-N && mkdir -p /tmp/relean-N
    cp -rs ~/.flt-release-lake/build/lib /tmp/relean-N/          # symlink farm, 0.3 s
    LEAN_PATH="/tmp/relean-N/lib/lean:$LP" LEAN_SRC_PATH="$LSP" \
      lean -DmaxErrors=200 Fermat/FLT/.../YourModule.lean
`~/.flt-release-lake/build` is the last PUBLISHED release, so it is green and consistent
with itself by construction; `lake env printenv` is required because `lake env lean`
resets `LEAN_PATH` and silently discards your prefix.
**State the caveat, because it is real and it is narrow.** That run does not see the cone
modules that changed between the release and `merger`. It is nevertheless the *relevant*
check for new text whose every dependency is declared EARLIER IN THE SAME FILE, which is
the usual shape of a decomposition — and it is a complete check on the rest of the file
too, in the weaker sense that it proves the file elaborates against SOME consistent
environment. Here it returned `EXIT=0` with zero errors and 13 `declaration uses 'sorry'`
warnings on a 37 000-line module, which is exactly the evidence a decomposition needs:
the old leaf's warning is gone and the new leaf's is present.
Two riders.
* **`tools/merge/frontier.py` hardcodes `ROOT = /home/chend/flt-staging`.** Running it from
  your worktree silently scans the MERGE WORKER'S tree and reports its leaves with its line
  numbers — the same trap as `flt-hidden-sorries.py`
  ([[flt-hidden-sorries-scans-main-repo]]), and it is much harder to notice here because
  the answer *looks* like your file. For a single-file leaf count, read the
  `declaration uses 'sorry'` lines out of your own `lean` log instead; that is the
  compiler and it costs nothing extra.
* **`git diff HEAD~1 HEAD -- <file> | grep -E '^[+-] *sorry *$'` is the one-line receipt
  for a RECUT.** One `+  sorry` and one `-  sorry` is the mechanical form of "count
  unchanged, 1 → 1", and it belongs in the commit message next to the prose claim, for the
  reason the RECUT section above gives: a warning-set delta of −1 +1 is otherwise
  indistinguishable from one closure plus one unrelated disclosure.
