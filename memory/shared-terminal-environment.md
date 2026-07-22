---
name: shared-terminal-environment
description: Environment specifics of the uni shared-terminal machine the repo moved to on 2026-07-22
metadata: 
  node_type: memory
  type: project
  originSessionId: 69cda54b-e063-41f5-976e-ff7d77392a99
  modified: 2026-07-22T14:55:46.095Z
---

Since 2026-07-22 the repo lives at `/home/chend/flt-lean` on a shared
uni terminal service (Linux, NFS home, no sudo, no docker).

**Why:** the CLAUDE.md/handoff assumptions from the old Mac no longer
hold; several were worked around during setup.

**How to apply:**
- brew python is externally-managed → use `.venv` at the repo root
  (has `bs4`, `curl_cffi`, `ocrmypdf`); `.mcp.json` runs annas-mcp
  with `.venv/bin/python`.
- `ANNAS_KEY` is in the gitignored `.env` at repo root
  (`set -a; source .env` for CLI use); mirror `--domain-index 2`
  works when the default mirror throws TLS errors.
- No docker: OCR = `.venv/bin/ocrmypdf` + system tesseract with
  `TESSDATA_PREFIX=~/.local/share/tessdata` (eng+fra+osd + configs
  copied there; the override dir must contain EVERYTHING tesseract
  needs, incl. `configs/`).
- Sources are in gitignored `sources/` (see SOURCES.md); the
  pre-split dissertation repo checkout at `~/dissertation` holds the
  old FLT git history and ATAEC under `Books/` (extract via
  `git show b4452f8:Books/...`).
- Reference Lean repo: shallow clone at `~/cs/FLT`.
- Working pattern: the driving Claude session runs in tmux session
  `agent2` (launched with `--dangerously-skip-permissions` and
  `/remote-control`, key exported); see [[stop-hook-tmux-restart]].
