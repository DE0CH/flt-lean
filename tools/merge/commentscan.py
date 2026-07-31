#!/usr/bin/env python3
"""Nesting-aware block-comment scanner.

`checks.py check-comment` walks LINES and clears a block at the first line
containing `-/`.  That model is blind to the two shapes that have actually cost
release rounds:

  * a RUNAWAY `/--` whose terminator a merge dropped.  Lean's block comments
    NEST, so some stray `-/` further down closes it and the file still PARSES
    while every declaration in between is silently a comment.  Release 27's
    X0.lean lost 46 declarations this way and the line-granular scan reported
    the declaration count UNCHANGED across the repair.
  * a STRAY `-/` at depth zero -- the mirror defect, where a merge kept one
    side's terminator and the other side's prose landed after it as bare Lean.
    Lean reports this as `unexpected token; expected ':'`, nothing about
    comments at all.

Both are invisible to a depth-BALANCE check, because a file with one of each
balances to zero.  So this scanner reports the two independently:

  UNCLOSED <file> <line>   a `/-` or `/--` still open at end of file
  STRAY    <file> <line>   a `-/` seen while depth was already zero

Character-level, and it honours `--` line comments at depth 0 (which may
legitimately contain `/-`), string literals, and nesting.

Usage: commentscan.py <file>...        exit 1 if anything is reported
"""
import sys


def scan(path):
    text = open(path, encoding="utf-8").read()
    lines = text.split("\n")
    depth = 0
    opens = []            # stack of 1-indexed line numbers of unmatched `/-`
    strays = []           # 1-indexed line numbers of `-/` seen at depth 0
    for ln0, line in enumerate(lines):
        i, n = 0, len(line)
        in_str = False
        while i < n:
            c = line[i]
            if depth == 0 and not in_str:
                if c == '"':
                    in_str = True
                    i += 1
                    continue
                if c == "\\" and in_str:
                    i += 2
                    continue
                if line.startswith("--", i):
                    break                      # rest of the line is a comment
                if line.startswith("/-", i):
                    depth += 1
                    opens.append(ln0 + 1)
                    i += 2
                    continue
                if line.startswith("-/", i):
                    strays.append(ln0 + 1)     # closes nothing
                    i += 2
                    continue
                i += 1
            elif in_str:
                if c == "\\":
                    i += 2
                    continue
                if c == '"':
                    in_str = False
                i += 1
            else:                              # inside a block comment
                if line.startswith("/-", i):
                    depth += 1
                    opens.append(ln0 + 1)
                    i += 2
                elif line.startswith("-/", i):
                    depth -= 1
                    opens.pop()
                    i += 2
                else:
                    i += 1
        if in_str:
            in_str = False                     # Lean strings do not span lines
    return opens, strays


if __name__ == "__main__":
    bad = 0
    for p in sys.argv[1:]:
        try:
            opens, strays = scan(p)
        except Exception as e:                 # noqa: BLE001 - report and continue
            print(f"ERROR    {p}: {e}")
            bad += 1
            continue
        for ln in opens:
            print(f"UNCLOSED {p} {ln}")
            bad += 1
        for ln in strays:
            print(f"STRAY    {p} {ln}")
            bad += 1
    sys.exit(1 if bad else 0)
