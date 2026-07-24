#!/usr/bin/env python3
"""Count tasks in the fleet FIFO queue (~/.flt-task-queue).

Tasks are chunks of text delimited by lines consisting exactly of
`=== TASK ===`. The head task may or may not carry a leading
delimiter (the pop hook strips the head chunk), so the truthful count
is the number of non-empty chunks after splitting on delimiter lines
— not the number of delimiter lines.

Usage: python3 queue-len.py [path]   (default: ~/.flt-task-queue)
Prints a single integer. Crashes loudly on a missing file.
"""

import os
import sys

path = sys.argv[1] if len(sys.argv) > 1 else os.path.expanduser("~/.flt-task-queue")
with open(path, encoding="utf-8") as fh:
    lines = fh.read().split("\n")

chunks = 0
current_nonempty = False
for line in lines:
    if line.strip() == "=== TASK ===":
        chunks += current_nonempty
        current_nonempty = False
    elif line.strip():
        current_nonempty = True
chunks += current_nonempty

print(chunks)
