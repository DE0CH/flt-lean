---
name: flt-sign-git-commits
description: "Deyao 2026-07-21: sign git commits in the FLT project from now on; stop passing --no-gpg-sign"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: a9c0eb39-e62e-4ff6-bd25-8f304bca8b98
---

In the FLT worktree (`~/cs/flt-worktree/fermat`), commits must be SIGNED from
2026-07-21 onward: run plain `git commit` (the repo config `commit.gpgsign=true`
with `gpg.format=ssh` signs automatically) and never pass `--no-gpg-sign`.
Existing unsigned commits are fine as they are — no history rewriting.

**Why:** signing had failed earlier in the session, so commits were made with
`--no-gpg-sign` as a workaround; Deyao asked (2026-07-21) to sign future
commits, and a live test confirmed ssh-signing now works at commit time (the
`%G? = N` on verification is only a missing `gpg.ssh.allowedSignersFile` for
local verification, not a signing failure).

**How to apply:** in every `git commit` for this project, simply omit
`--no-gpg-sign`. If a commit ever fails due to signing, surface the error to
Deyao instead of silently falling back to unsigned. Related:
[[wstar-top-down-dependency-tree]].
