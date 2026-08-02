---
name: flt-sorry-grep-returns-zero
description: "The `declaration uses 'sorry'` grep returns 0 on Lean 4.32 — it emits BACKTICKS, and the warning prefix swaps sides between lake build and lake env lean"
metadata: 
  node_type: memory
  type: project
  originSessionId: 60ba0bb4-3044-477d-ab03-d0378b13c9c2
  modified: 2026-08-02T02:28:12.330Z
---

Measured 2026-08-02 (`flt-lean-225`, Lean 4.32.0-rc1, commit `b4812ae5`) on a
green `lake build` log of `X0.lean`'s cone containing **164** sorry warnings:

    grep -c "declaration uses 'sorry'"   ->    0     <- the recipe CLAUDE.md quotes ~15 times (and `~/.flt-agent-doctrine.md` ~10 times)
    grep -c 'declaration uses `sorry`'   ->  164     <- what Lean actually writes

Two independent axes break the usual recipes, and each silently yields `0`:

* **quoting** — Lean writes the token in BACKTICKS, not single quotes;
* **prefix side** — `lake build` writes `warning: <path>:<l>:<c>: …` (prefix
  first), `lake env lean` writes `<path>:<l>:<c>: warning: …` (location first).
  So `^warning:` scores 164 / **0** and `: warning:` scores **0** / 2.

Robust, and validated: `grep -cE 'declaration uses .sorry.' <log>` — no prefix
anchor, quote-agnostic dot. Checked against `flt-frontier.py`'s source scan on
the same tree: `X0.lean` **101 = 101**, and across all **23** modules the build
reached, **164 warnings, zero mismatches in either direction**.

**Why it survived:** the *scripts* are safe. `flt-buildfrontier.py` already
parses `declaration uses .sorry.`, and `.claude/check-sorries.py` reads
`sorryAx` from the environment, not message text. Only the hand-typed recipe
breaks — and CLAUDE.md instructs agents to type it as the ground-truth
cross-check for every frontier scan. Run today it compares 380 rows against 0.

**Why:** a counting recipe whose failure mode is `0` is indistinguishable from
the healthy answer, so nothing reports it. This is the third instance in this
project after `EXIT=127` (missing `lake` on `PATH`) and the error-count recipe
(`': error(\(|:)'` returns 0 on a `lake build` log — see
[[flt-error-count-recipe-returns-zero]]).

**How to apply:** validate any inherited counting recipe against a case with a
KNOWN NONZERO answer before trusting a zero from it. Never validate it on a tree
you believe is clean — that direction cannot tell a working grep from a broken
one. Related: [[flt-frontier-tools-hardcode-staging-root]].
