#!/usr/bin/env python3
"""Re-enable the Stop hook safely after the setup session ends.

Must be run DETACHED (setsid/nohup) so it survives step 1. Order
matters (Deyao, 2026-07-22): the setup session must die BEFORE the
hook is re-enabled, otherwise its own turn-end triggers the freshly
re-enabled check-sorries hook and traps it in the blocked-stop loop.

1. kill the setup session's tmux session (agent-0)
2. rename _DISABLED_Stop -> Stop in .claude/settings.json
3. type "continue" into the worker session agent2
"""
import json
import subprocess
import sys
import time

SETUP_SESSION = sys.argv[1] if len(sys.argv) > 1 else "agent-0"
SETTINGS = "/home/chend/flt-lean/.claude/settings.json"

# 1. kill the setup tmux session (the session running this script's parent)
subprocess.run(["tmux", "kill-session", "-t", SETUP_SESSION], check=False)
time.sleep(2)

# 2. re-enable the Stop hook
with open(SETTINGS) as f:
    settings = json.load(f)
hooks = settings.get("hooks", {})
if "_DISABLED_Stop" in hooks:
    hooks["Stop"] = hooks.pop("_DISABLED_Stop")
    with open(SETTINGS, "w") as f:
        json.dump(settings, f, indent=2)
        f.write("\n")

# 3. nudge agent2 so it picks up the config and keeps looping
subprocess.run(["tmux", "send-keys", "-t", "agent2", "-l", "continue"], check=False)
time.sleep(1)
subprocess.run(["tmux", "send-keys", "-t", "agent2", "Enter"], check=False)
