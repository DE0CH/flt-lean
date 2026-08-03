## A STALE `.lake` MAKES A PRESENT DECLARATION LOOK SWALLOWED — and the contradiction is the tell
(2026-08-02, `flt-lean-80`.) A worktree fast-forwarded 2242 commits still had a
`.lake/build` from two days earlier. A scratch module that `public import`ed
`MazurTorsion.lean` then reported `Unknown identifier
Fermat.exists_coordinateRingAlgEquiv_compat_of_isWeierstrassModel` for a theorem that is
plainly at `X0.lean:20829` in the source — while `Fermat.exists_variableChange_of_isWeierstrassModel`,
declared 1500 lines BELOW it in the same file, resolved fine.
That combination reads exactly like a **runaway doc comment**: a declaration present in the
source, absent from the environment, with its neighbours fine. I ran the comment-depth scan
(the right instinct) and it said **depth 0 at that line and total depth 0 for the file** —
i.e. real code, no wound. **That contradiction is the diagnosis, not a puzzle**: a
comment-nesting scan reads the SOURCE and an `Unknown identifier` reads the OLEAN, so when
they disagree the olean is from a different source. One `stat` on the olean settled it
(mtime two days before the sources), and
`rsync -a --delete ~/.flt-release-lake/build/ .lake/build/` — 69 s — made all three names
resolve.
**So the order of checks when a scratch cannot see a declaration you can read:**
    stat -c '%y %n' .lake/build/lib/lean/<the declaring module>.olean   # older than your ff?
    git diff --stat $(cat ~/.flt-release-lake/sha) HEAD -- Fermat/      # empty => rsync is exact
and only then reach for `commentspan.py` / `parsecheck.py`. The doctrine already says to
rsync after a fast-forward; what is new is that **skipping it produces a false SWALLOWED-
DECLARATION report**, which is one of the most expensive wrong diagnoses in this tree
because it sends you into another module's merge history.
Corollary for the enumeration trick itself, which is worth keeping: to find a declaration's
real namespace, do not guess and do not grep for `^namespace` (this project's docstrings say
"namespace" in prose). Ask the environment:
    run_cmd do
      let env ← Lean.getEnv
      for (n, _) in env.constants.toList do
        if (n.toString.splitOn "<distinctive fragment>").length ≥ 2 then Lean.logInfo n.toString
Ten seconds, and it returns the fully-qualified name. It is also the check that exposed the
stale olean, because it returned the *neighbours* and not the target.
