## A background `ssh … lake build` reported STOPPED may still be RUNNING — relaunching gives TWO builds in one worktree
(2026-07-31.) A `run_in_background` Bash whose task record is lost across a session
boundary comes back as `stopped` / "no completion record was found … it may have been
running when the previous Claude Code process exited". **That is a statement about the
harness's bookkeeping, not about the remote process.** The `ssh` client died; the remote
`bash -c '… lake build …'` did not. Relaunching the same command then puts **two
concurrent `lake build`s in one worktree**, racing on one artifact directory.
The symptom is a build failure that reads as a broken tree and is not:
    ✖ [4970/4976] Building Fermat.FLT.Modularity.AmpleSheaf
    error: no such file or directory (error code: 4294967294)
      file: …/.lake/build/lib/lean/Fermat/FLT/Modularity/AmpleSheaf.olean
— one `lake` moves the temp olean away from under the other. Two further tells, both
observed: **two `lean` workers elaborating the SAME file**, and a log that `grep` calls
`binary file matches`, because both builds opened it with `>` and the second's truncation
left the first writing at its old offset into a NUL-padded hole (use `grep -a`, and a
FRESH log filename per launch — a reused one cannot be told from the previous run's).
So before relaunching any remote build, look for a live one, and kill by PID only after
checking the cwd (the host runs ~40 other worktrees):
    ssh $H 'for p in $(pgrep -x "lake|lean"); do
              case "$(readlink /proc/$p/cwd)" in $HOME/flt-lean-N) echo "$p";; esac; done'
Killing a `lake` **orphans its `lean` children**, which keep elaborating and keep writing
oleans into that same tree — kill those by PID too, or the "replacement" build races the
corpse of the one it replaced. And note the harness may report the survivor as your
*failed* job (exit 143) when you kill what you think is the stray: the two are
indistinguishable from the tool side, which is the whole reason to check `/proc` rather
than reason from task ids.
