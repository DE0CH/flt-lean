---
name: stop-hook-tmux-restart
description: How the Stop hook was disabled for setup and how to re-enable it safely (detached script pattern)
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 69cda54b-e063-41f5-976e-ff7d77392a99
  modified: 2026-07-22T14:37:23.733Z
---

During the 2026-07-22 machine move Deyao had the Stop hook disabled by
renaming the `Stop` key to `_DISABLED_Stop` in
`.claude/settings.json` (claude ignores unknown hook events with a
startup warning; the config is preserved in place).

**Why:** on the shared machine a Stop hook that runs a potentially
40-minute build on every turn-end "will not go well" during setup;
and a session that re-enables the hook while still running can trap
ITSELF in the blocked-stop loop.

**How to apply:** re-enable only from a DETACHED script
(setsid/nohup, survives tmux kill) that (1) kills the setup session's
tmux session first, (2) renames `_DISABLED_Stop` back to `Stop`,
(3) `tmux send-keys` "continue" into the worker session (`agent2`) so
it picks the config up. Never re-enable the hook from inside the
session that is about to stop. Script used:
`.claude/reenable-stop-hook.py` ([[shared-terminal-environment]]).
