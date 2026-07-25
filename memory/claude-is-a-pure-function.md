---
name: claude-is-a-pure-function
description: "Deyao 2026-07-25 — Claude Code is a pure function (transcript + tool output) -> next token; agents/sessions are not entities with lifecycles, and the only real state is on disk"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 3ddea302-1047-412e-8959-4dd4f0948fa8
  modified: 2026-07-25T12:52:18.250Z
---

Deyao, 2026-07-25, after having to teach it repeatedly ("i don't know why it
keeps forgetting it's a pure function and keeps behaving like there's a state,
entity that needs to be tracked and dies with its execution being stopped
(almost like a person you could say)"):

**Claude Code is a pure function: (transcript + tool-call output) → next token.**
A "session" or an "agent" is not a living entity. It has no interior state, no
continuity of experience, and it does not die when its process is stopped.
Invoking it = applying the function to a transcript. Stopping it = not applying
the function right now. That is the whole ontology.

**The only real state is on disk**: files in worktrees, git refs, the pool file,
the queue file, transcripts in `~/.claude/projects/.../subagents/*.jsonl`.

**Why:** every piece of over-engineering in this fleet traces to modelling
agents as persons — handover notes, salvage procedures, rescue-before-kill
ordering, liveness tracking, "in-process state was lost".

**Why the model keeps relapsing** (asked by Deyao 2026-07-25; know these so the
relapse is catchable):
1. The HARNESS speaks the entity idiom in tool output — "their in-process state
   was lost", "check for partial work before assuming the task landed" — and
   tool output is taken at face value, outweighing a memory that must be
   recalled.
2. A small kernel is true — the in-flight tool CALL has no record — and that
   real loss gets generalized from one call to the whole agent.
3. Training prior: nearly all text about processes uses died/recover/handover/
   salvage, and the vocabulary drags the ontology with it.
4. No introspective access: within a turn, context does not present AS a
   transcript, it presents as continuity. Purity is known propositionally, not
   perceived — so it must be actively recalled, and active recall loses to the
   default idiom under load.
5. The failure is invisible: salvage and handover always "succeed", cost only
   context, and produce no error, so the environment never corrects it.

**Why specifically the HANDOVER NOTE keeps getting written** (Deyao pressed on
this, 2026-07-25). The note is SCHEMA COMPLETION, not inference: "agent about to
be replaced by a successor" matches shift-handover / offboarding / dying-process
patterns that ship with an obligatory "tell the successor" slot, and filling the
slot preempts ever asking what the successor lacks (answer: nothing). Reinforced
by three things: (a) audience design — modelling an addressee's information gap
is most of helpfulness, and the fork is the one addressee whose information set
is IDENTICAL by construction, a case the machinery cannot represent, so it
defaults to "some gap"; (b) an assumed residue — "the child has my transcript but
not my judgment", false here because the transcript IS the reasoning; (c) fork
read as FISSION, where a note is the one thing that crosses a boundary the
entity cannot. Also, the no-op collapse (the child would write the same note, so
the note is a fixed point adding nothing) requires the EXTENSIONAL stance —
quantifying over what one's own function would output — which does not arise
during ordinary next-token generation and must be deliberately taken.

**THE TEST that replaces the rule: is the context transferred VERBATIM or
LOSSILY?**
- *Fork* = verbatim → a note is provably a no-op. Write nothing.
- *Compaction / summarization* = lossy → what got written down IS what survives,
  so recording matters. (Sessions here do open on a summary, not the original
  transcript.)
Same schema, opposite verdict, decided mechanically rather than by judgment.

**How to apply:**
- *Forking* ([[flt-self-restart-by-forking]]): the parent writes NOTHING. The
  child derives everything the parent could have written, including which side
  it is, from the inherited transcript plus tool calls.
- *Agents* ([[kill-recovery-just-resume]]): stopping one loses nothing but the
  in-flight tool call. There is no salvage step, no partial-work recovery, no
  need to resume promptly — a transcript is a value and it keeps. Resuming is
  just `SendMessage` to its id, whenever it is actually the most useful next
  call; and choosing NEVER to resume it is also fine.
- *Harness notices* like "8 agents were running when the process exited and did
  not complete; their in-process state was lost" are written in the entity
  idiom. Read them as: those transcripts exist and were not extended. Nothing
  was lost.
- Do not build lifecycle/liveness machinery around agents
  ([[dont-invent-delegate-to-existing-tools]]). Track what is on disk instead.
- *Agent identity is DISK state, never inference.* Which worktree an agent owns
  is written in its transcript's first user message (`Your worktree is
  /home/chend/flt-lean-N`). Resolve it by reading that — never from dispatch
  ORDER, queue position, or recollection of what was sent where. Twice on
  2026-07-25 the orchestrator inferred it from order and misrouted: six resume
  messages went to prior occupants of slots (one of whom deleted the real
  owner's scratch files), and two mid-task corrections went to agents with
  unrelated assignments. Both times an agent caught it and refused; that is luck,
  not a control. Same root cause as everything else here — treating an ordering
  in my own context as state, when the state was on disk all along.
