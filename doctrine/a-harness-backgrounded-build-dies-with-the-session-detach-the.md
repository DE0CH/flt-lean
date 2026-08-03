## A HARNESS-BACKGROUNDED BUILD DIES WITH THE SESSION — detach the BUILD, keep the WAITER

(2026-07-31, measured twice in one run.) The doctrine rule "plain foreground command, no
`nohup`, no `setsid`, no `&`, set the Bash tool's `run_in_background`" is about not losing the
NOTIFICATION. It does not protect the WORK: a `lake build` started that way is a child of the
harness, and when the session restarts between turns — context compaction does this — the
child is killed. Both times the notification arrived saying "no completion record was found …
it may have been running when the previous Claude Code process exited", and both times a
~25-minute build was thrown away at 4926/4929 modules.

The shape that survives both failure modes is to split them:

    setsid nohup bash -c '... lake build ... > LOG 2>&1; echo EXIT=$? >> LOG; touch DONE' \
      < /dev/null > /dev/null 2>&1 &          # the WORK, detached, survives a restart
    until [ -f DONE ]; do sleep 20; done      # the WAITER, harness-backgrounded, wakes you

The waiter is cheap and disposable — if it dies with the session, re-arm it and the build is
still there. This is not a reversal of the doctrine rule: a self-detached job with NO waiter
is still the thing that strands agents. Detach the expensive half, track the cheap half.

