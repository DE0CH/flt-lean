## THE TOKEN IN YOUR PROMPT GOES STALE ON RESUME — read the job file before writing the sentinel

(2026-07-31, `flt-lean-175`, caught by accident.) A prover agent's ONLY output channel is
`~/.flt-loop/jobs/<name>.sentinel`, and `flt-loop.py` accepts it only if its `token` equals the
token in `jobs/<name>.json` **at harvest time**:

    if d.get("token") == j["token"]:   j["sentinel"] = d      # else: no sentinel at all

The comment beside it says why — *"Resume mints a new token precisely so the old marker goes
inert."* So when a session is RESUMED (the record grows `retries`, `resume: true`, a fresh
`spawned_at`, and `<name>.started` is rewritten with the new token), the token printed in the
prompt text you are still reading belongs to the PREVIOUS incarnation. A sentinel copying it
"verbatim", exactly as the prompt instructs, is discarded whole: the loop then sees
`started ∧ ¬alive ∧ ¬sentinel`, concludes the agent died, and dispatches a replacement that
starts from nothing. **The commits survive on the branch; the `queue` and `to_merger` do not.**

This is invisible from inside the agent. Nothing announces the respawn, the prompt is not
re-read, and the sentinel write succeeds — the file is there, correctly formed, and simply never
matches. It was found here only because a `ls` of the jobs directory happened to show a
`.started` file newer than the sentinel.

So, as the last step before writing the sentinel — always, not only when you suspect a resume:

    python3 -c "import json;print(json.load(open('$HOME/.flt-loop/jobs/<name>.json'))['token'])"

and use THAT. It agrees with the prompt on a first run and disagrees on every resumed one. Same
check applies to a merge worker or medic, whose sentinels carry `panic` / `go` fields that gate
the whole loop.

Corollary for whoever maintains the loop: an agent cannot be asked to copy a value that the loop
may rotate underneath it. Either the prompt should be rewritten on resume (it is — `.prompt` is
regenerated, but a running session never re-reads it), or the sentinel should be matched on the
job's identity rather than on a value the agent must echo.

