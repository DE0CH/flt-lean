## A TASK PROMPT CAN BE BUILT ON A **DECLINED** PAYLOAD — the premise then lives in ONE COMMIT and on NO BRANCH
(2026-08-02, `flt-lean-55`, on `exists_dedekind_rigidifiedModuli` in `X0.lean`.)
This file already covers three ways a prompt can describe a tree you do not have: the
target is proven on `merger` and not on `main`; the target was CUT on an unmerged
branch; your worktree is stale.  There is a fourth, nothing above covers it, and it is
the only one where **merging something cannot help you** — the prompt's PREMISE was
DECLINED at merge.
My task was to split a leaf "along the descent line that already exists", naming five
declarations (`SpecZinv`, `hom_ext_specZinv`, `existsUnique_classify_of_isPullback`,
`exists_isAffine_rigidifiedModuliSchemeData_baseChange`, `…_zinv`) as PROVEN and
available.  All five have **zero occurrences anywhere in the tree**, and every ordinary
diagnosis of that is wrong here:
* `main` and `merger` were the SAME commit (release 33 had just published), so the
  release-window check returns "you are current";
* the worktree was current after one fast-forward, so the stale-checkout check passes;
* `git log --all -S SpecZinv` DOES find the creating commit `f2eaf03d`;
  `git merge-base --is-ancestor f2eaf03d main` returns **YES**; and
  `git branch --contains f2eaf03d` lists **every branch in the pool**.
So by ancestry the work is present and by grep it is absent.  **The command that
resolves it is the one with `-m`**, because the removal happened on one side of a merge:
    git log -m --oneline -S '<the name>' --all -- <path>
Two lines came back, and the second is the entire answer:
    9bc0599c (from f2eaf03d) Merge flt-lean-366 -- X0.lean payload DECLINED, superseded by flt-lean-346
    f2eaf03d X0: DESCEND the F_l Katz-Mazur citation to Z[1/n], where Katz-Mazur states it
**The merge worker did everything right** — it declined a superseded payload and said so
in the subject line, which is exactly the receipt the DECLINE-IS-A-COMMIT rule asks for.
What manufactured the phantom task is that the queue entry was written from the DECLINED
BRANCH'S OWN REPORT, which described its branch truthfully and could not know it would
not be taken.  **Every branch report is a description of a branch, and roughly one branch
per release is declined; so this will recur.**
Three things follow.
* **A `TARGET:` naming machinery you cannot find is not automatically a stale worktree.**
  Run the `-m` log before merging anything.  If the answer is a decline, no merge will
  ever help, and `git merge merger` — the standard remedy for the other three classes —
  is a no-op that costs you the diagnosis.
* **Do NOT recover the declined machinery.**  It was declined because something better
  landed, so re-adding it manufactures a duplicate cut; here it would also be
  FREE-FLOATING, since the superseding route consumes none of it.  `git show f2eaf03d`
  keeps it recoverable if a consumer ever appears — say so, and move on.
* **Check whether the task's GOAL was met by the superseding route before reporting
  anything.**  Here it was, and by a STRICTLY MORE GENERAL route: the declined branch
  descended one citation to `ℤ[1/n]`, while the surviving family states it at an
  ARBITRARY ring with `n` and `N` invertible, which subsumes `ℤ[1/n]`, `ℚ` and `𝔽_ℓ` at
  once.  **"Superseded by X" in a decline message is a claim worth reading**: it names
  the thing that makes your task unnecessary, and reading it is the difference between
  "my premise is missing" and "my premise was replaced by something better".
**And write the finding into the surviving leaf's own docstring, not only into the
sentinel.**  The declined names are unqueryable, but the SURVIVING leaf's name is what a
queue audit keeps: `exists_dedekind_rigidifiedModuli` is still open, so this task passes
every existence filter and WILL be re-dispatched.  A paragraph at the leaf is the only
thing that stops the next agent repeating the whole investigation — the sentinel reaches
one merge worker, the docstring reaches everyone after.
