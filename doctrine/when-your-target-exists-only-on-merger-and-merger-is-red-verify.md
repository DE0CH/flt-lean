## WHEN YOUR TARGET EXISTS ONLY ON `merger` AND `merger` IS RED: VERIFY IN A SCRATCH AGAINST THE RELEASE OLEANS
(2026-07-31, `flt-lean-189`.) The release-window rule says to run
`git show merger:<file> | grep -n <name>` before your first edit. Do it — but be
ready for the answer that costs a whole strategy: **the leaf exists ONLY on
`merger`, and `merger` does not build.** Release 27 did not publish precisely
because `merger`'s `X0.lean` carries **103 errors**, and `X0` is in the import
cone of `ModThree`, so `lake build Fermat.FLT.…ModThree` on a merger-based branch
cannot even reach the module you were sent at.
Three facts to have in advance, because each of them costs a build cycle to learn:
* **You must base on `merger` anyway.** The target declaration, its docstring, its
  proven neighbours and the parent that consumes it are all merger-only; landing
  the same work on `main` manufactures a rival cut and a duplicate declaration.
  `git merge merger` into your branch, and say so in the commit subject.
* **`main` and the release snapshot are the same tree for Lean purposes.** Check it
  (`git diff --stat $(cat ~/.flt-release-lake/sha) main -- Fermat/` empty) and then
  `~/.flt-release-lake/build/lib/lean` is a *fully consistent* olean set — the only
  consistent one you have, since your own `.lake` is now a mix of main-seeded and
  merger-built artifacts.
* **A symlink farm of it is the fast loop, and it is 12 SECONDS.** `cp -rs` the
  release lib into `/tmp`, put it FIRST on `LEAN_PATH`, and compile a scratch that
  `public import`s the target module. Measured here: **12 s per round** against a
  `lake build` that cannot complete at all.
      cp -rs ~/.flt-release-lake/build/lib/lean /tmp/relean-N/lib/
      LP=$(lake env printenv LEAN_PATH); LSP=$(lake env printenv LEAN_SRC_PATH)
      LEAN_PATH="/tmp/relean-N/lib/lean:$LP" LEAN_SRC_PATH="$LSP" lean ScratchN.lean
  (`lake env lean` RESETS `LEAN_PATH`, so harvest with `printenv` and call bare
  `lean` — the existing note about this is exactly right and easy to skip past.)
**The soundness condition, and it is checkable rather than a matter of taste:**
restate the target VERBATIM in the scratch and prove it there. Every name your
proof uses must then exist, with the same statement, at the release sha. Here that
was `IsNarrowRayEquivMod`, `FractionalIdeal.count` and Chebotarev's
`tsum_rpow_neg_absNorm_ne_top` — all older than the release, all unchanged
(`git diff --stat main merger -- <their files>` empty). What the scratch does NOT
prove is that the merger file's *other* 5 000 new lines still elaborate; say so.
**The hybrid farm, when you want more than the scratch.** To elaborate the real
merger file, build the farm from YOUR `.lake` (merger oleans for everything the
failed build did produce) and drop the RELEASE copy of just the broken module over
it. One module substituted, and the failure mode is loud (`unknown constant`,
arity mismatch) rather than silent. Copy **all** the sibling artifacts, not just
the `.olean`: Lean also opens `X0.olean.server` and will stop with
`failed to open file … .olean.server` if you copy only the first one.
    cp -rs $PWD/.lake/build/lib/lean /tmp/relean-Nb/lib/
    for e in olean olean.hash olean.server olean.server.hash \
             olean.private olean.private.hash ir ir.hash; do
      cp -f ~/.flt-release-lake/build/lib/lean/<path>/X0.$e /tmp/relean-Nb/lib/lean/<path>/
    done
And do **not** substitute a module whose merger olean built fine — here `X1` also
differs between `main` and `merger`, its merger olean existed, and overwriting it
with `main`'s would have been a gratuitous inconsistency. Substitute exactly the
modules that are missing.
**Compute the blast radius before believing any of it**: walk the target's import
closure and intersect it with `git diff --name-only main merger -- Fermat/`. Here
that was **43 of 198** modules — which is the honest reason the scratch, not the
hybrid farm, is the primary evidence.
### Three Lean traps measured in the same session
* **`Set.indicator_of_mem h` picks the WRONG indicator when the goal has two.**
  Passing the bare membership proof lets Lean unify the set with the first
  occurrence, and you get `h1 has type ¬w.asIdeal ∣ mm but is expected to have
  type w ∈ {w | ¬… ∧ …}`. Pin the set with `show`:
  `rw [Set.indicator_of_mem (show w ∈ {w | ¬ w.asIdeal ∣ mm} from h1)]`.
* **`tsum_subtype _ _` does not unify `{w // p w}` with `↥{w | p w}`** at the
  metavariable stage — it reports a `Type mismatch` displaying two identical-looking
  `tsum`s. Supply both explicit arguments (the set and the function). Same for
  `Equiv.subtypeSubtypeEquivSubtypeInter`, which additionally leaves an unreduced
  `(e c)` in the term so a following `rw` finds no pattern; the indicator route
  (`tsum_subtype` on both sides plus one pointwise case split) is the one that works.
* **`ENNReal.rpow_ne_top_of_ne_zero`'s implicit is `x`, not `a`** — and supplying it
  as a named argument inside a `rw [ENNReal.tsum_toReal_eq (fun w => …)]` is enough
  to blow the 200 000-heartbeat budget with a `whnf` timeout. Prove the per-term
  `≠ ⊤` as its own `have` over the subtype first and pass that; the timeout goes away
  and no heartbeat bump is needed for it.
