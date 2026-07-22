---
name: scripts-crash-dont-fallback
description: "Deyao 2026-07-22 — scripts in general must NOT contain fallbacks; on anything unexpected, throw an exception that crashes the script — the caller (usually Claude) is the right place to handle it"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 8e948ad7-2925-4f81-a46b-38fef37021d4
  modified: 2026-07-22T19:36:02.388Z
---

Deyao (2026-07-22): "this applies to scripts in general … when something is not expected, do not have fallbacks, throw an exception that crashes the script. this is because most likely, claude is using the script and the exception handling is best done by the caller claude."

**Why:** A script's fallback bakes one fixed, context-free recovery policy into code, silently converting failures into wrong-but-plausible output (the 2026-07-22 progress-tree cache-fallback rendered a silently rearranged tree instead of the correct loud "ModThree does not compile"). The caller — Claude reading the traceback — has context the script lacks: it can diagnose, choose a recovery, re-dispatch, or escalate to Deyao. A loud crash with a specific message is the most informative interface between script and caller.

**How to apply:** In every script (python or otherwise): validate assumptions and `raise` with a precise message when they fail; no try/except that degrades to partial output, no synthetic defaults for missing data, no "keep going with a note". Let exceptions propagate to a nonzero exit and a real traceback. Exceptions to the rule are only where Deyao explicitly wants harmlessness (e.g. the Stop hook fails open — but even there: real answer or silence, never synthetic data). Related: [[flt-report-blocker-class]], [[scripts-get-a-server-not-mcp]].
