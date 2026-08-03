## `pgrep -f "lake build <Module>"` COUNTS YOUR OWN SHELL AND EVERY OTHER WORKTREE
(2026-07-31, and it cost a 25-minute elaboration.) Checking for rival builds with
    pgrep -u chend -f "lake build Fermat.FLT.FreyCurve.MazurTorsion" | wc -l
returned **5**, and `pgrep -f "[l]ean .*MazurTorsion.lean"` returned **3**. Both were
wrong in the same two ways. The harness wraps every Bash call in
`bash -c '… eval "pgrep -f …" …'`, so the pattern matches the *asking* shell — the
`[l]ean` bracket trick defeats self-matching only for the bare word, not for a
pattern that also appears inside the wrapper's own command line. And the module
path is not worktree-qualified, so it matches `~/flt-lean-342`'s build of the same
file. There was exactly ONE real process, and it was mine and healthy.
Reading that as "rival elaborations" led to `pkill` plus deleting the `.olean` and
`.trace` — destroying a build that was 13 minutes in and had nothing wrong with it.
So: **always filter, and always qualify by worktree**:
    pgrep -af "flt-lean-50.*MazurTorsion" | grep -v "bin/bash"
Separately, and the reason the panic was plausible: **background Bash waiters do not
survive a harness restart**, and each restart delivers a "no completion record …
marked stopped" notification that looks like the *build* died. It did not — the
`lean` child kept running with a new ppid. Re-arming a waiter each time works, but
the robust shape is to detach the build itself so nothing can reap it:
    setsid --fork bash -c 'cd ~/flt-lean-N && lake build M > /tmp/b.log 2>&1; echo "EXIT=$?" >> /tmp/b.log' < /dev/null
then poll for the `EXIT=` marker you wrote yourself. Never conclude a build finished
from the absence of errors in the log.
