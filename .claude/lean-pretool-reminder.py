#!/usr/bin/env python3
"""PreToolUse hook on mcp__report-flt-lean* tools (Deyao, 2026-07-23):
before a diagnostics(file_path) call, mechanically check that file for
unused have/let bindings via textDocument/documentHighlight (a binder
whose only reference is its own definition site is unused -- LSP
scope-correct, not a regex heuristic: the regex only finds CANDIDATE
positions, the LSP decides usage) and surface any found via
additionalContext.

WARN-ONLY (Deyao, explicit correction 2026-07-23): this must never
block the tool call -- permissionDecision is always "allow".

Anonymous `have : P := ...` (binds `this`, no explicit name) is out of
scope -- there is no identifier to query.
"""

import importlib.util
import json
import os
import re
import sys

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
HOME = os.path.dirname(REPO_ROOT)
REPORT_MCP_PATH = os.path.join(REPO_ROOT, "report-mcp.py")

STATIC_REMINDER = (
    "Before calling Lean, please check that sorry is only used in place "
    "of a proof (never a proposition) and that every have/let is "
    "comsumed. You may not define a have that is not used anywhere."
)

# Candidate discovery only: `have <ident> :` / `have <ident> :=` /
# `let <ident> :` / `let <ident> :=`. The LSP decides actual usage.
BINDER_RE = re.compile(r"\b(?:have|let)\s+([A-Za-z_][A-Za-z0-9_']*)\s*:")


def _load_pipe_lsp():
    spec = importlib.util.spec_from_file_location("report_mcp", REPORT_MCP_PATH)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod.PipeLsp


def _find_binders(text):
    out = []
    for lineno, line in enumerate(text.splitlines()):
        for m in BINDER_RE.finditer(line):
            out.append((m.group(1), lineno, m.start(1)))
    return out


def _worktree_path(tool_name):
    parts = tool_name.split("__")
    if len(parts) < 2 or not parts[1].startswith("report-flt-lean"):
        return None
    worktree_name = parts[1][len("report-"):]
    return os.path.join(HOME, worktree_name)


def _check_unused(worktree_path, file_path, timeout=180):
    abs_path = (
        file_path
        if os.path.isabs(file_path)
        else os.path.abspath(os.path.join(worktree_path, file_path))
    )
    if not os.path.exists(abs_path):
        return None  # let the real diagnostics call raise "file not found"

    text = open(abs_path, encoding="utf-8").read()
    binders = _find_binders(text)
    if not binders:
        return []

    PipeLsp = _load_pipe_lsp()
    socket_dir = os.path.join(worktree_path, ".report-server")
    lsp = PipeLsp(socket_dir)
    lsp.diagnostics(abs_path, timeout=timeout)  # ensure fully elaborated
    uri = "file://" + abs_path

    unused = []
    for name, line, col in binders:
        result = lsp._request(
            "textDocument/documentHighlight",
            {
                "textDocument": {"uri": uri},
                "position": {"line": line, "character": col},
            },
            timeout,
        )
        if result is not None and len(result) <= 1:
            unused.append((name, line + 1))
    return unused


def main() -> int:
    # GRACEFUL policy (Deyao's caller principle): this hook is
    # harness-called and its absence/failure must never break a tool
    # call. Any error in the mechanical check is reported to stderr and
    # skipped; the plain reminder still goes through.
    try:
        payload = json.load(sys.stdin)
    except Exception as exc:
        sys.stderr.write(
            f"lean-pretool-reminder: could not parse hook input ({exc!r}); "
            "emitting the reminder anyway.\n"
        )
        payload = {}

    context = STATIC_REMINDER
    tool_name = payload.get("tool_name", "")
    tool_input = payload.get("tool_input", {})

    if tool_name.endswith("__diagnostics"):
        worktree_path = _worktree_path(tool_name)
        file_path = tool_input.get("file_path")
        if worktree_path and file_path:
            try:
                unused = _check_unused(worktree_path, file_path)
            except Exception as exc:
                sys.stderr.write(
                    f"lean-pretool-reminder: unused-have check failed "
                    f"({exc!r}); skipping.\n"
                )
                unused = None
            if unused:
                listing = "; ".join(f"`{n}` (line {l})" for n, l in unused)
                context += (
                    f"\n\nMECHANICAL CHECK: unused have/let binding(s) found "
                    f"in {file_path}: {listing}. Consume them or delete them "
                    f"before considering this proof done."
                )

    print(
        json.dumps(
            {
                "hookSpecificOutput": {
                    "hookEventName": "PreToolUse",
                    "permissionDecision": "allow",
                    "additionalContext": context,
                }
            }
        )
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
