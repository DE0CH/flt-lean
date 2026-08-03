## `run_in_background: true` DOES NOT SURVIVE THE CLAUDE PROCESS — use `setsid --fork` for any long build
(2026-07-31, `flt-lean-270`, twice in one run.) The doctrine file offers two shapes for a long
build and says shape 1 — a plain foreground command issued with `run_in_background: true` — is
safe because "the harness owns the lifetime". **It owns it only as long as the harness is alive.**
A 45-minute `lake build` launched that way was killed twice when the Claude process was restarted
mid-turn, each time leaving a log that ends mid-stream with **no `EXIT=` line** — the exact
signature the doctrine warns about, produced by the *recommended* shape rather than by a bad one.
The fix costs one wrapper and is unconditional for anything over a few minutes:
    setsid --fork bash -c 'cd ~/flt-lean-N && export PATH="$HOME/.elan/bin:$PATH" \
      && lake build <Mod> > /tmp/b.log 2>&1; echo "EXIT=$?" >> /tmp/b.log' </dev/null >/dev/null 2>&1
    # verify ppid: `ps -o pid,ppid,sid -p <pid>` must show ppid 1
    # then poll IN-TURN for the EXIT= line; a run_in_background waiter dies with the harness too
Both halves matter. The build must be `ppid 1`, **and** the waiter must not be the only thing
holding the result — a `run_in_background` poll loop is killed by the same event that kills a
`run_in_background` build, so it reports nothing and looks identical to a hang. Poll in-turn.
Also: `lake` is **not on PATH** in a fresh non-login shell here (`lake: command not found`,
`EXIT=127` in under a second). `export PATH="$HOME/.elan/bin:$PATH"` inside the wrapper, not
outside it.
