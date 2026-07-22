---
name: scripts-crash-dont-fallback
description: "Deyao 2026-07-22 — the error policy of a script follows its CALLER: Claude-called scripts crash loudly (no fallbacks; Claude handles exceptions); harness/Deyao-called scripts (Stop hook) need reasonable graceful fallbacks instead"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 8e948ad7-2925-4f81-a46b-38fef37021d4
  modified: 2026-07-22T19:38:59.590Z
---

Deyao (2026-07-22): "when something is not expected, do not have fallbacks, throw an exception that crashes the script. this is because most likely, claude is using the script and the exception handling is best done by the caller claude." Same day, on the Stop hook: "that principle does not apply to the stop hook script, because if you think about it, the stop hook is called by me, not you" — "so that needs to have reasonable fallbacks."

**The principle is caller-directed error policy:**
- **Caller = Claude** (generators, checkers, servers, helpers Claude invokes): NO fallbacks. Validate assumptions, `raise` with a precise message, let the traceback propagate to a nonzero exit. Claude reads it, diagnoses with context the script lacks, chooses recovery. A fallback here silently converts failure into wrong-but-plausible output (the 2026-07-22 progress-tree cache-fallback rendered a silently rearranged tree instead of a loud "ModThree does not compile").
- **Caller = harness/Deyao** (the Stop hook, fired at turn boundaries): reasonable graceful fallbacks REQUIRED. A traceback there is noise dumped on a human. Unexpected conditions degrade to a sensible outcome (allow the stop silently or with one short informative line); never a raw traceback, never a block from made-up data, never synthetic counts — real answer or graceful silence.

**How to apply:** When writing or reviewing any script, first ask WHO calls it, then apply the matching policy. Related: [[flt-report-blocker-class]], [[scripts-get-a-server-not-mcp]], [[flt-stop-hook-is-a-nudge]].
