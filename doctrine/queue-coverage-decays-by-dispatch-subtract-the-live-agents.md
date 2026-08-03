## QUEUE COVERAGE DECAYS BY DISPATCH — SUBTRACT THE LIVE AGENTS BEFORE REPORTING A GAP
(Same run.) A release verifies its coverage invariant against the queue **as
installed**. The loop then pops tasks FIFO, so by mid-cycle the queue is a fraction
of what was installed — here `queue1` had drained 385 → 134 — and a naive re-run of
the coverage check reports every dispatched leaf as UNCOVERED.
Measured on my two modules: **17 leaves uncovered by `queue1` + `queue2`, of which
14 were held by a live agent and 3 were genuinely unowned.** Reporting the 17 would
have been alarmist and wrong; reporting the 3 is a real result.
So the check has three terms, not two:
    UNOWNED = frontier − queue1 − queue2 − {leaves named in LIVE agents' prompts}
and "live" is `jobs/<name>.started` present with `jobs/<name>.sentinel` absent. Grep
each live job's `.prompt` **and** `.json` (the payload is in the json; the prompt
file can lag), and match on the last dotted component with a trailing dot stripped.
The corollary is what makes this worth running at all: **a coverage gap found
mid-cycle is a gap the release audit could not have seen**, because the leaves that
fall through are the ones cut *after* the audit — freshly-cut residues of work that
landed in the same release. All three of mine were cut on 2026-07-31, the day before.
