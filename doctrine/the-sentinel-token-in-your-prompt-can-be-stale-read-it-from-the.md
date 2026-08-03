## THE SENTINEL TOKEN IN YOUR PROMPT CAN BE STALE — READ IT FROM THE JOB RECORD

(2026-07-31, `flt-lean-310`. Caught with four commits already on the branch and the
sentinel already written under the wrong token.)

Every prover agent is told: *"`token` — copy it verbatim or the loop ignores the whole
file."* That is true, and the token printed in the prompt is **not always the one the
loop will accept.**

`flt-loop.py` accepts a sentinel whose token is `j["token"]` **or** a member of
`j["prev_tokens"]` (line ~883). Its comment says a resumed job is the same job, so an
earlier incarnation's result is still its result.

**CORRECTED 2026-07-31 (`flt-lean-81`): `prev_tokens` IS written now, and the paragraph
that used to stand here — "nothing ever writes it, it is always `None`" — is FALSE at the
current `flt-loop.py`.** Measured on a live job: `token af3e18a7`,
`prev ['9297f07f', '1e2d779d']`, `resume True`, `retries 1`, and the prompt's token was
`9297f07f`, i.e. the FIRST entry of `prev_tokens`. `flt-loop.py:1038` even carries a
comment saying that a missing `prev_tokens` "panicked the loop on its first resume", so
the field is now maintained deliberately. **Do not conclude from the old paragraph that a
prompt token is certainly dead — but do not rely on `prev_tokens` either.** The advice
below is unchanged and is still the right thing to do, because `j["token"]` is what
line 1039 overwrites the accepted sentinel's token with, and it is the only value
guaranteed to match.

**CORRECTED 2026-07-31 (`flt-lean-395`): `prev_tokens` IS written now, and the
prompt's token therefore works again.** The original finding above was right when
made — the field was read and never populated, so a resumed agent's prompt token was
dead. It has since been fixed: `flt_loop_rows.py:504–505` does

    j["prev_tokens"] = ((j.get("prev_tokens") or []) + [j["token"]])[-10:]
    j["token"] = tok()

on every resume, and `flt-loop.py:883` matches against that list. Measured on this
job: prompt token `6df72ed9`, live token `8460ee68`, and
`prev_tokens = ['6df72ed9', '21670961']` — so the prompt's token would have been
accepted. Note the grep that produced the original verdict now finds **four**
occurrences and the two new ones are in a DIFFERENT FILE, which is why re-running it
against `flt-loop.py` alone still looks like the bug is live. Grep both files.

**The recommendation below is unchanged, and is now belt-and-braces rather than
essential**: write the token the RECORD holds. It is accepted under either
implementation, it costs one command, and it does not depend on a fix staying in
place.

**CORRECTION (2026-07-31, `flt-lean-311`): `prev_tokens` IS NOW POPULATED, so a stale
prompt token is no longer fatal.** This paragraph used to read "`grep -n prev_tokens
flt-loop.py` finds exactly two occurrences … **nothing ever writes it**, it is always
`None`", and that was true when written. The writer now exists — `flt_loop_rows.py:504`,
`j["prev_tokens"] = ((j.get("prev_tokens") or []) + [j["token"]])[-10:]` — so on resume
the retiring token is pushed onto a ten-deep history and `flt-loop.py:883` accepts it.
Measured on this job: prompt token `d23a0878`, live token `d9605e97`,
`prev_tokens = ['d23a0878']`, i.e. the prompt's token *would* have been accepted.

**The procedure below does not change and is still the one to follow** — read the token
from the record, not the prompt. What changes is the SEVERITY: a sentinel written from a
stale prompt is now normally accepted rather than silently discarded, so an agent that
skipped the check has probably not lost its work. Do not go hunting for a lost sentinel
on that theory alone; check `prev_tokens` first. And note the general shape, which is the
reason this correction is worth its own paragraph: **a section of this file that reasons
from the ABSENCE of a line in a tool's source is a measurement of that source on one day,
and the fleet's own tooling is under active repair.** Re-run the grep before believing it,
exactly as with every "absent from the pin" claim.

**CORRECTED 2026-07-31 (`flt-lean-115`): `prev_tokens` IS populated now.** A resumed job
observed on that date read `token: 0028aee5, prev_tokens: ['4f1d1581'], retries: 1,
resume: true`, with `4f1d1581` being exactly the token its prompt carried. So the
fallback the loop reads really does fire, and copying the prompt's token verbatim on a
resumed job is no longer fatal. **Do not relax the check on that account.** The
canonical value is still `j["token"]` — the loop overwrites the sentinel's token with it
at line 1039 — the field could stop being written again as easily as it started, and
reading it costs one command. Cross-check `j["session"]` against your own session id
while you are there; it is the second, independent confirmation that you are the live
owner rather than a discarded twin.

**CORRECTED 2026-07-31 (evening), `flt-lean-281`: `prev_tokens` IS populated now.**
Measured on a live record — prompt token `491e5dc5`, `j["token"] = e25b121a`,
`j["prev_tokens"] = ['491e5dc5', '31a6a9f1']`, `resume: true`. So on that job a sentinel
written with the PROMPT's token would have been accepted after all. **Read the two
clauses separately, because only one of them changed**: the *mechanism* (resume rotates
the token, the prompt is never re-read) is unchanged and is what makes the check
necessary; the *consequence* ("a stale token is discarded outright") is now softened by
`prev_tokens`. Do not rely on the softening — a two-generation-old token, or a loop
version that stops recording, puts you back in the original hole. The one-command check
below still costs nothing and still gives the right answer either way; write
`j["token"]`.
**CORRECTED 2026-07-31 (`flt-lean-314`): `prev_tokens` IS populated now.** Measured on a
live resumed job — `token = fca8a17e`, `prev_tokens = ['9ba77c10', '6262e7ec',
'd46875f2']`, `resume = True`, `retries = 1` — so the loop has since been fixed and a
stale prompt token is in fact accepted. **This does not make the check optional**, for
two reasons: a job resumed more times than the list retains, or a future regression in
the writer, puts you straight back in the silent-discard failure; and reading the record
also gives you `session`, which is the independent confirmation that you are the live
owner rather than a discarded twin ([[flt-loop-spawn-liveness-race]]). Read the record,
write `j["token"]`, and treat agreement with your prompt as the thing you verified
rather than the thing you assumed.
**CORRECTED 2026-07-31 (`flt-lean-325`), measured rather than grepped: `prev_tokens` IS
populated.** That worktree's `jobs/flt-lean-325.json` read
`token = 9b53d9c6`, `prev_tokens = ['c409d64f', 'b4e2c3b0']`, `resume = true` — and
`c409d64f` was exactly the token printed in the prompt, i.e. the fallback path really does
cover the stale-prompt case on that job. So the failure this section describes is REAL in
shape and is **not guaranteed** to fire; a sentinel written from a stale prompt token may
be accepted after all. Do not let that soften the rule: `prev_tokens` is a fallback whose
population you cannot check without reading the file, and reading the file is the whole of
the recommended procedure anyway. **Read `token` from the job record and write that** — it
is correct whether or not the fallback exists, and it costs one command. The grep that
produced the "always `None`" claim was reading the wrong writer; treat a claim about
`flt-loop.py`'s behaviour derived from grepping it as a hypothesis, exactly like every
other absence claim in this file.
**CORRECTED 2026-07-31 (`flt-lean-95`): `prev_tokens` IS written now, and the safety net
it provides is real.** Measured on a live resumed job:
`{'token': 'dacb1063', 'prev_tokens': ['1256ab5b', 'b2168cd5'], 'resume': True}`, with the
prompt still carrying `1256ab5b` — i.e. the loop had rotated the token TWICE and kept both
old ones. So a sentinel copied verbatim from the prompt would have been accepted after all.
**The advice below is unchanged and should still be followed**: read the token from
`jobs/<name>.json` / `<name>.started` rather than from the prompt, because the fallback is
somebody else's implementation detail and was absent for at least one release. What changes
is only the diagnosis if you find your work discarded — an unaccepted sentinel is no longer
the likeliest cause.
Meanwhile resume mints a NEW token, deliberately, so the old `.started` marker goes
inert. The agent's prompt is the ORIGINAL payload and still carries the ORIGINAL token.
So on any job with `resume: true` / `retries > 0`:
**CORRECTED 2026-07-31 (`flt-lean-361`): `prev_tokens` IS written, and the claim that
stood here — "`grep -n prev_tokens flt-loop.py` finds exactly two occurrences, nothing
ever writes it, it is always `None`" — was FALSE.** The grep was right and was run on the
wrong file: the writer is `flt_loop_rows.py:504`,
`j["prev_tokens"] = ((j.get("prev_tokens") or []) + [j["token"]])[-10:]`, immediately
above the `j["token"] = tok()` that mints the new one. Measured live on a resumed job:
`token: 9ef851a2`, `prev_tokens: ['15c0921e']`, and `15c0921e` was exactly the token
printed in that run's prompt. So the old token is accepted and a resumed agent's sentinel
is **not** discarded.
**The lesson generalises past the loop, and it is why the correction is worth more than
the fact: a claim of the form "nothing writes X" is a claim about a SEARCH, and the
search's scope is part of the claim.** This project's loop is two modules —
`flt-loop.py` (the state machine) and `flt_loop_rows.py` (the row actions that mutate the
job records) — and essentially every WRITE lives in the second. Grep the directory, not
the file whose name matches the concept. Same failure shape as the self-certifying greps
recorded above, at tooling scope instead of Lean scope.
Resume still mints a NEW token, deliberately, so the old `.started` marker goes inert, and
the agent's prompt is the ORIGINAL payload carrying the ORIGINAL token. So on any job with
`resume: true` / `retries > 0`:
**FIXED SINCE, AND THE PARAGRAPH THAT WAS HERE IS NOW FALSE — do not act on it**
(re-measured 2026-07-31, `flt-lean-96`). This section used to say that
`grep -n prev_tokens flt-loop.py` finds only a read and a field-copy, that **nothing ever
writes it**, and that it is always `None`. It is written now, by
`flt_loop_rows.py:504` — `j["prev_tokens"] = ((j.get("prev_tokens") or []) + [j["token"]])[-10:]`
— on every resume, keeping the last **10**. Measured on a live record: my prompt carried
`beb58f3b` while `j["token"]` was `a9d91d5d` and
`j["prev_tokens"] == ['beb58f3b', '505e23d5']`, so the prompt's token would have been
accepted. The rule below is unchanged and still worth following; what changes is that
getting it wrong is now recoverable rather than fatal, and an agent that notices the
mismatch should NOT read it as evidence that the loop is broken.
Resume mints a NEW token, deliberately, so the old `.started` marker goes inert. The
agent's prompt is the ORIGINAL payload and still carries the ORIGINAL token. So on any job
with `resume: true` / `retries > 0`:

* the live token is in `~/.flt-loop/jobs/<name>.json` and `<name>.started`;
* the prompt's token is the pre-resume one, and is now in `prev_tokens`;
* **either is accepted.** The failure this section was written to prevent — a sentinel
  ignored, `j["sentinel"]` left `None`, and `started ∧ ¬alive ∧ ¬sentinel` making the loop
  conclude the agent died and dispatch a replacement at work already committed — is
  therefore no longer live. Only the last ten tokens are kept, which is far more than any
  job's retry count.
* the prompt's token is the pre-resume one;
* a sentinel written under the prompt's token is accepted **only while that token is still
  inside the 10-deep `prev_tokens` window** — beyond that it is rejected, `j["sentinel"]`
  stays `None`, and `started ∧ ¬alive ∧ ¬sentinel` makes the loop conclude the agent
  **died**.

**Read the record anyway.** It costs one command, it is the only thing that stays right if
the retention window or the acceptance rule changes again, and the `prev_tokens` safety net
is itself a fix that this file asserted did not exist for a day.
That residual failure is still the worst shape this file catalogues: completed, committed,
compiler-verified work thrown away, and a replacement dispatched at leaves that are already
proven — a phantom dispatch manufactured out of a *successful* run. It just now needs ten
resumes rather than one.

**The lesson that outlives the fix: a claim in this file about what the LOOP'S SOURCE does
is dated evidence in exactly the way a claim about the Lean tree is.** `flt-loop.py` and
`flt_loop_rows.py` are edited daily and the loop re-execs onto the edited source itself. Two
`grep`s cost seconds and settle it; quoting this file settles nothing.

**So the check is one command, run it before writing the sentinel:**

    python3 -c "import json;j=json.load(open('/home/chend/.flt-loop/jobs/<name>.json'));print(j['token'], j.get('prev_tokens'))"
    cat /home/chend/.flt-loop/jobs/<name>.started

**Write the token the RECORD holds, not the token the prompt holds.** If they agree,
nothing is lost by having checked. If they disagree, the record wins — the loop reads
`j["token"]` out of that file and compares against it, and line 1039 shows the loop
itself overwrites the sentinel's token with `j["token"]` once it accepts one, which
settles which of the two is canonical.

This is NOT a `to_medic` case on its own: the workaround is one line and an agent that
performs it lands its work normally. It is a `to_merger` note, and it belongs here so the
next agent does not have to rediscover it with its branch already committed.

Generalisation, and it is the same shape as "a `sorry` is a PROMISE" and "ancestry is not
content": **a value handed to you in a prompt is a claim about state at dispatch time, not
state now.** Prompts are immutable; the state machine is not. Anything in a prompt that
names live state — a token, a line number, a leaf that is "still open", a worktree said to
be owned by someone else — is a hypothesis to check against the state itself.

