## A PROMPT'S "THIS MODULE IS RED" IS DATED — ASK THE OLEAN, NOT THE PROMPT
(Same run.)  The task prompt warned, in detail and with eight line numbers, that
`X0.lean` was RED and that a full build would produce no olean, so the work
should be judged by "absence of errors in your line range".  That was true on
`merger` on 2026-07-31.  It was false two days later: release 33 published with
X0's cone green, and the task's own advice would have thrown away the fast loop.
**The check is one `ls`, and it beats any amount of reasoning about the prompt:**
    ls -la $(git rev-parse --show-toplevel)/.lake/build/lib/lean/<Module path>.olean
An olean that exists and is newer than the last release means the module built.
Here `X0.olean` was 17.5 MB and dated after the release, so a scratch that
`public import`s it verified the whole cluster in **7 seconds** per round against
a ~9-minute full build — and the full build then went green first try, `Build
completed successfully (5308 jobs)`, zero errors.
Same family as every other dated-evidence rule in this file, with the cheapest
possible instrument: the artifact, not the prose.
