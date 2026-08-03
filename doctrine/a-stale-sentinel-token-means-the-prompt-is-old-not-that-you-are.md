## A STALE SENTINEL TOKEN MEANS THE PROMPT IS OLD, NOT THAT YOU ARE DISCARDED

(2026-07-31, flt-lean-107. Caught one tool call before the sentinel would have been thrown
away with a finished, green, committed task inside it.)

`~/.flt-loop/jobs/<worktree>.json` rotates `token` on every retry. A RESUMED agent
(`"resume": true`) is handed its original transcript, so **the token in its prompt is the
token of the incarnation that was resumed, not the one the loop is now keyed on.** Mine said
`0194f666`; the job said `fceb21ba`. The prompt is explicit that a mismatched token makes the
loop ignore the whole file — so writing the prompt's token would have registered a completed
two-leaf proof as a death and dispatched retry 10 at work already committed.

`[[flt-loop-spawn-liveness-race]]` says to check your token against `jobs/<name>.json`, and it
reads a mismatch as "you are a discarded incarnation, yield without writing your sentinel".
That is one of TWO causes and, on a resumed job, the less likely one. Both must be
distinguished before you write anything, and neither the token nor `pgrep` alone does it —
`pgrep -af flt-job` lists every worker on the host, and a `pgrep` for your own token matches
your own command line, so it never returns zero.

**The decisive check is your own process ancestry**, because the loop names each worker
process after the token it issued it:

    P=$$; for i in 1 2 3; do P=$(ps -o ppid= -p $P | tr -d ' '); \
      ps -o args= -p $P | cut -c1-40; done      # -> "flt-job-<token>"

If that token equals `jobs/<name>.json`'s, **you are the live owner and the prompt is stale**:
write the sentinel with the JOB's token. Cross-check `session` in the same file against your
own session id — the loop records it, and it is a second independent confirmation. Only if the
ancestry names a DIFFERENT token than the job file are you the discarded twin, and then you
yield silently.

Corollary, and the reason this is worth a section: the failure is invisible from inside. A
sentinel written with a stale token is not rejected, not logged, and not retried — it is
ignored, and the loop's own timeout is what eventually notices. Everything downstream then
looks exactly like an agent that died mid-task, including to the next agent reading the
worktree, which will find the branch already carrying the proof and no record of who wrote it.

