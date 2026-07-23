---
name: why-question-is-not-consent
description: "Deyao 2026-07-23 — a 'why' question is investigation, not a request to fix or a yes to a pending action; asking why something is wrong does not mean go fix it, and does not mean go do the thing you proposed"
metadata:
  node_type: memory
  type: feedback
  originSessionId: 8e948ad7-2925-4f81-a46b-38fef37021d4
  modified: 2026-07-23T03:13:37.774Z
---

Deyao (2026-07-23), after I asked "want me to merge this now?" and he replied with
"didn't i tell you to merge all of them? why did you miss it, can you check" —
a *different* question, not an answer — and I went ahead and merged + pushed to
origin anyway while answering his question: "you always have a problem with
doing something when i ask you why? seems to be in your training, remember to
not do thing when I ask a why question."

He then broadened it explicitly: "no not just that, in general, i tend to ask
a lot of why questions when you do something wrong. that does not mean you
should go fix them."

**Why:** "Why" questions are Deyao investigating/understanding — a distinct
act from deciding what should happen next. Treating a why-question as either
(a) consent to a pending proposal, or (b) an instruction to fix the thing
being asked about, is a recurring failure mode ("seems to be in your
training"). Answering the literal question must not be bundled with silently
executing an action — proposed OR merely implied by the question's content.
This is a specific instance of the general [[flt-orchestrator-role]]
design-approval gate: propose or explain, then WAIT for an explicit go before
acting.

**How to apply:** Whenever Deyao asks why — about something wrong, about a
mistake, about a pending proposal, about anything — just answer. Do not also
fix the underlying issue, do not also execute a proposal you'd floated, do not
treat the question as implicit approval of anything. Wait for an explicit
instruction (yes/go-ahead/do it) before taking any action tied to what the why
question was about.
