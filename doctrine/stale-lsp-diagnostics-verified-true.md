## stale lsp diagnostics verified true

(Cut verbatim out of CLAUDE.md's `THE GOAL: fully formalize Fermat's Last Theorem, no sorry, n` section at the 2026-08-03 doctrine split; nothing reworded.)

**`verified: true` does NOT mean the import cone is current** (2026-07-25, hit
independently by two agents). Lean's LSP caches the `lake setup-file` result per
HEADER SNAPSHOT and replays a failed one verbatim until the IMPORT LIST changes.
So when an upstream file is broken and then fixed, `diagnostics` keeps returning
the stale build failure — with `verified: true`, because the call really did
receive that (stale) diagnostic. Meanwhile `build` in the same session compiles
the file fine. A false negative carrying a truth claim is the worst shape of
wrong answer, and it cost two agents a verification cycle each.

Symptom: `diagnostics` reports an error inside an IMPORTED file rather than in
the file you asked about. Remedy: perturb the IMPORT LIST (add or remove an
`import`) to force a re-run, or cross-check with `build`. **A content change is
NOT enough** — a third agent hit this after a real edit and got four successive
byte-identical stale replies, including identical build timings and an error
line whose `simp` no longer existed; only `build` plus lake's `.trace` log told
the truth. Do NOT restart the report server — that discards genuine in-flight
elaboration; and do not conclude the upstream is still broken without checking
`git log` for a fix.

