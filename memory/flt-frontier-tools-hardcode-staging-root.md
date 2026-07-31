---
name: flt-frontier-tools-hardcode-staging-root
description: tools/merge/frontier.py hardcodes ROOT=/home/chend/flt-staging, so from any other worktree it silently reports the MERGE WORKER's frontier instead of yours
metadata:
  type: project
---

`tools/merge/frontier.py` (added release 27, and the one the handover says is
validated against the compiler 25/25) begins

    ROOT = pathlib.Path('/home/chend/flt-staging')

so running it from a prover worktree scans the **merge worker's staging tree**,
not the tree you are editing. It prints paths relative to that root, so the
output looks exactly like a scan of your own worktree and nothing warns you.

Measured 2026-07-31 from `flt-lean-119`: it reported my edited leaf
`exists_hilbertAuxDiamondGenerators` as still open at its OLD line number, while
that line in my file was the middle of a docstring — and its totals differed by
five leaves across `DifferentialCharacter`, `ProjectiveEquationAdd2`,
`ShortExact`, `EllipticScheme` and `HyperellipticJacobian`, because staging was
mid-release with **uncommitted conflicted files** (`git status` there showed
`UU CLAUDE.md`, `UU Fermat/FLT/Modularity/MoretBailly.lean`).

Fix, and it costs one line:

    sed "s|ROOT = pathlib.Path('/home/chend/flt-staging')|ROOT = pathlib.Path('$PWD')|" \
      tools/merge/frontier.py > /tmp/frontier.py && python3 /tmp/frontier.py

Same class as [[flt-hidden-sorries-scans-main-repo]] — this is the SECOND fleet
scanner with a hardcoded root, so treat it as the default hypothesis for any
`flt-*`/`tools/merge/*` script: **grep it for an absolute path before believing
its numbers.** A leaf-count that disagrees with your own file is a wrong-root
check first and a real disagreement second.
