## YOU CAN VERIFY AN EDIT INSIDE A FILE THAT HAS 178 ERRORS — `-DmaxErrors`, THEN A SHIFT-INVARIANT DIFF

(2026-07-31, `X0.lean` at release 28.) The doctrine's "diff the shim against the
unedited file" recipe assumes you can at least reach your own edit. In a giant red
module you cannot, and the reason is a default nobody thinks about: **`maxErrors` is
100, and Lean ABORTS elaboration when it trips.** `X0.lean`'s errors start at line
4889 and the cap fired at 74693 — so everything below that, including both of the
edits under test at 94158 and 94685, was simply never elaborated, and the build log
says nothing at all about them. That reads as "no news", and no news here is no
information.

    lake env lean -DmaxErrors=4000 Fermat/FLT/ModularCurve/X0.lean

took it to the end of the file (113 errors reported, max line 107958) and put both
edits in reach. Do this before concluding that a red file cannot be worked in.

**Then diff SHIFT-INVARIANTLY, or the diff is unreadable.** Any insertion moves every
later error, so a naive line-set comparison reported 85 "new" and 83 "gone" errors on
an edit that introduced none. Key each error by `(column, message)` instead of by line,
compare the two multisets, and separately confirm the line offsets fall into a few
constant buckets:

    baseline 178 errors, mine 177
    offsets: 0 (×87), +31 (×34), +60/+61 (×3)     <- exactly what was inserted, and where
    only in mine:     `timeout at whnf` (col 39), `unknown metavariable ?_uniq.3080446`
    only in baseline: `timeout at isDefEq` (col 39), `?_uniq.3080066`,
                      `Tactic decide proved that the proposition … is false` (col 35)

Two of those three pairs are NOISE and you must recognise them or you will chase them:
a pre-existing heartbeat timeout reports its phase as `isDefEq` or `whnf` depending on
which unification ran first, and a `?_uniq.NNNNNNN` metavariable id is a global counter
that any edit shifts. The third is the real result — the `decide` that the edit fixed.
So the honest verdict was "zero errors introduced, one removed, and the sorry-warning
count 96 → 95", each number checkable by anyone from two logs.

**And the baseline swap is safe if your work is committed first**: `cp` your file
aside, `git checkout <parent> -- <path>`, elaborate, `cp` back, then `git add` the path
— that last step matters, because the `checkout` STAGED the old version and `git status`
will read `MM` until you do. Confirm with `git show HEAD:<path> | md5sum` against the
worktree file before you stop.

