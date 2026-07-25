#!/usr/bin/env python3
"""PostToolUse hook on mcp__report-flt-lean*__diagnostics (Deyao,
2026-07-23): after every diagnostics call, mechanically check the
queried file for unused have/let bindings and surface any via
additionalContext.

POST-tool-use and STRICTLY READ-ONLY by design: the real diagnostics
call has just synced (didOpen/didChange) and fully elaborated the
document under report-mcp.py's single consistent version history, so
this hook only sends textDocument/documentHighlight queries against
the already-open document. It never sends didOpen/didChange -- a
second stateless client racing the MCP server's document versions is
exactly the defect behind the 2026-07-23 duplicate-elaboration
incident, and the read-only contract removes that bug class
structurally rather than trying to synchronize two version counters.

Method: regex finds CANDIDATE binder positions only ("have <ident> :",
"let <ident> :"); the LSP decides actual usage via documentHighlight
-- exactly 1 highlight (the definition site alone) means unused; 0
means the position is not a real identifier (e.g. inside a comment),
skipped; 2+ means used. Columns are converted to UTF-16 code units as
LSP requires (math identifiers make lines non-ASCII). Anonymous
`have : P := ...` (binds `this`) is out of scope -- no identifier to
query.

GRACEFUL (harness-called): any failure exits silently; never blocks.
"""

import fcntl
import importlib.util
import json
import os
import re
import sys

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
HOME = os.path.dirname(REPO_ROOT)

# Candidate names: anything non-space up to the `:` of the type
# ascription (or of `:=`). Lean identifiers are broad unicode (hσρ, hΦ,
# hμne, h₁'...), so the class is permissive; obvious non-identifiers
# (anonymous-constructor patterns, `_`) are filtered after the match,
# and the LSP is the real judge anyway (0 highlights = not an
# identifier = skipped).
BINDER_RE = re.compile(r"\b(?:have|let)\s+([^\s:⟨(]+)\s*:")


def _utf16_col(line, codepoint_col):
    return sum(2 if ord(c) > 0xFFFF else 1 for c in line[:codepoint_col])


def _worktree_path(tool_name):
    parts = tool_name.split("__")
    if len(parts) < 2 or not parts[1].startswith("report-flt-lean"):
        return None
    return os.path.join(HOME, parts[1][len("report-"):])


def _check(worktree_path, file_path):
    abs_path = (
        file_path
        if os.path.isabs(file_path)
        else os.path.abspath(os.path.join(worktree_path, file_path))
    )
    if not os.path.exists(abs_path):
        return None

    lines = open(abs_path, encoding="utf-8").read().splitlines()
    binders = []
    for lineno, line in enumerate(lines):
        for m in BINDER_RE.finditer(line):
            name = m.group(1)
            if name == "_" or name.startswith("_"):
                continue
            binders.append((name, lineno, _utf16_col(line, m.start(1))))
    if not binders:
        return []

    spec = importlib.util.spec_from_file_location(
        "report_mcp", os.path.join(worktree_path, "report-mcp.py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    lsp = mod.PipeLsp(os.path.join(worktree_path, ".report-server"))

    uri = "file://" + abs_path
    unused = []
    with open(lsp.lock_file, "a+") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        lsp._connect()
        for name, line, col in binders:
            try:
                result = lsp._request(
                    "textDocument/documentHighlight",
                    {"textDocument": {"uri": uri},
                     "position": {"line": line, "character": col}},
                    timeout=30,
                )
            except Exception:
                continue  # e.g. document not open (failed diagnostics call)
            if result is not None and len(result) == 1:
                unused.append((name, line + 1))
    return unused


def _parsed_response(payload):
    """The report-MCP `diagnostics` result as a dict, or None."""
    resp = payload.get("tool_response")
    if isinstance(resp, list) and resp:
        resp = resp[0]
    if isinstance(resp, dict):
        content = resp.get("content")
        if isinstance(content, list) and content and isinstance(content[0], dict):
            text = content[0].get("text") or ""
            try:
                resp = json.loads(text)
            except Exception:
                return None
    return resp if isinstance(resp, dict) else None


def _has_error(payload) -> bool:
    """True if the file failed to elaborate.

    When elaboration fails, `documentHighlight` has no semantic information to
    return and falls back to at most the definition occurrence -- which this
    check would read as "exactly 1 highlight, therefore unused". That is a FALSE
    POSITIVE, and it fires precisely when an agent is already dealing with a
    broken build, i.e. at the worst moment. Observed 2026-07-25: `hN0` in
    `archConv_decay` was flagged unused while being consumed three times
    (`hN0.le` twice, `ne_of_gt hN0`), because the worktree's import cone was red
    from an unrelated file. So: no elaboration, no verdict."""
    resp = _parsed_response(payload)
    if not resp:
        return False
    diags = resp.get("diagnostics")
    if not isinstance(diags, list):
        return False
    # LSP DiagnosticSeverity: 1 = Error.
    return any(isinstance(d, dict) and d.get("severity") == 1 for d in diags)


def _false_clean_warning(payload) -> str:
    """An empty diagnostics list is only trustworthy when the call actually
    received the compiler's publish.

    `publishDiagnostics` is a one-shot notification to whichever client
    connection is attached at the time. A client that adopts an
    already-elaborated document from the shared open-document map and finds
    the content unchanged sends no notify, so `waitForDiagnostics` returns at
    once and the client's diagnostics table for that URI is empty -- which
    reads as "compiles clean". On 2026-07-25 an agent was told a file
    containing five sorries had zero diagnostics this way.

    report-mcp.py now returns `verified: true/false` for exactly this, but
    only client processes started after that fix carry it. So warn whenever an
    empty result arrives without an explicit `verified: true`."""
    resp = payload.get("tool_response")
    if isinstance(resp, list) and resp:
        resp = resp[0]
    if isinstance(resp, dict):
        content = resp.get("content")
        if isinstance(content, list) and content and isinstance(content[0], dict):
            text = content[0].get("text") or ""
            try:
                resp = json.loads(text)
            except Exception:
                return ""
    if not isinstance(resp, dict):
        return ""
    diags = resp.get("diagnostics")
    if diags != []:
        return ""
    if resp.get("verified") is True:
        return ""
    return (
        "DO NOT RECORD THIS AS A CLEAN VERIFICATION. The diagnostics list came "
        "back empty WITHOUT `verified: true`, which means UNKNOWN, not clean: "
        "the document may already have been elaborated in this server session, "
        "in which case the compiler's diagnostics went to an earlier client and "
        "cannot be replayed to yours. An agent was misled this way on "
        "2026-07-25 -- told a file with five sorries had zero diagnostics. To "
        "get a real answer, make an actual content change (even one docstring "
        "line) and call again; only new content starts new work and produces a "
        "fresh publish. Do not restart the report server -- that discards "
        "genuine in-flight elaboration."
    )


def main() -> int:
    try:
        payload = json.load(sys.stdin)
        tool_name = payload.get("tool_name", "")
        if not tool_name.endswith("__diagnostics"):
            return 0
        warning = _false_clean_warning(payload)
        if warning:
            print(json.dumps({
                "hookSpecificOutput": {
                    "hookEventName": "PostToolUse",
                    "additionalContext": warning,
                }
            }))
            return 0
        if _has_error(payload):
            return 0  # see _has_error: highlights are meaningless on a red file
        worktree_path = _worktree_path(tool_name)
        file_path = (payload.get("tool_input") or {}).get("file_path")
        if not worktree_path or not file_path:
            return 0
        unused = _check(worktree_path, file_path)
    except Exception as exc:
        sys.stderr.write(f"unused-binding-check: skipped ({exc!r})\n")
        return 0
    if not unused:
        return 0
    listing = "; ".join(f"`{n}` (line {l})" for n, l in unused)
    print(json.dumps({
        "hookSpecificOutput": {
            "hookEventName": "PostToolUse",
            "additionalContext": (
                f"MECHANICAL CHECK: unused have/let binding(s) in "
                f"{file_path}: {listing}. Every bound have/let must be "
                f"consumed (glue-first discipline) -- consume them or "
                f"delete them before considering this proof done."
            ),
        }
    }))
    return 0


if __name__ == "__main__":
    sys.exit(main())
