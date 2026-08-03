## A MANGLED `PATH` MAKES `lake` RE-CLONE MATHLIB AND DESTROY ITS BUILD — copy the PACKAGE back from a sibling worktree
(2026-08-01, `flt-lean-166`, self-inflicted, and the recovery is 25 seconds only
because the diagnosis is written down here.)
The standing rule is "`lake` is not on `PATH` in an agent shell; export
`$HOME/.elan/bin` first". A PATH that is mangled rather than merely missing is far
worse, and it costs a package. What I ran was
    export PATH=\$HOME/.elan/bin:\$PATH; export PATH=$HOME/.elan/bin:$PATH; lake env lean …
— the first export was written with ESCAPED dollars, so it set `PATH` to the literal
string `$HOME/.elan/bin:$PATH`, and the second prepended the real elan directory. Net
effect: **`lake` was on `PATH` and `/usr/bin` was not.** That call is the only thing
that ran between a worktree whose scratch module compiled in 7 s and one where
    info: mathlib: cloning https://github.com/leanprover-community/mathlib4
    info: mathlib: checking out revision 'a3364faec42918fcd84a03a255b50570129f9ead'
appeared and `.lake/packages/mathlib/.lake` **no longer existed** — the 6.4 G olean
build gone, the source re-fetched.
**The symptom names the wrong thing.** The next compile says
    error: unknown module prefix 'Mathlib'
    No directory 'Mathlib' or file 'Mathlib.olean' in the search path entries: …
followed by a search-path dump in which the mathlib entry is PRESENT. That reads as a
broken `LEAN_PATH` or a torn `.lake/build`, and it is neither: the directory in the
dump is real and empty. Check `ls .lake/packages/mathlib/.lake/build/lib/lean` before
reseeding anything, and read the FIRST lines of the log — `cloning` is never something
a healthy invocation does.
**Recovery is a copy from a sibling worktree, not `lake exe cache get` and certainly
not a rebuild.** Every worktree on the host is pinned to the same mathlib revision:
    cd /scratch/chend-flt/flt-lean-SIB/.lake/packages/mathlib && git rev-parse HEAD
    cd /scratch/chend-flt/flt-lean-N/.lake/packages/mathlib   && git rev-parse HEAD   # must match
    cp -a /scratch/chend-flt/flt-lean-SIB/.lake/packages/mathlib/.lake \
          /scratch/chend-flt/flt-lean-N/.lake/packages/mathlib/.lake
Measured: **25 seconds for 6.4 G** on machine-local scratch. Pick a sibling with no
live `lake`/`lean` whose `/proc/<pid>/cwd` is inside it, and note this is read-only on
their side, so it does not violate "do not touch another worktree".
Three things that would otherwise cost a cycle each:
* **`~/.flt-release-lake/build` does NOT contain mathlib.** It is the PROJECT build
  (`.lake/build`); the packages live in `.lake/packages/<pkg>/.lake/build` and are a
  separate tree. Reseeding the release snapshot fixes nothing here.
* **`Cli` has no build in ANY worktree, and that is normal** — it is only needed by
  `lake exe cache`. Do not chase it when auditing which package builds exist.
* **Audit all the packages, not just mathlib**, with one loop over
  `.lake/packages/*/.lake/build/lib/lean`; a partial wipe is possible and a missing
  package other than mathlib gives the same misleading message.
**The prevention is one habit: never write a `PATH` export with escaped dollars, and
put the export and the command in the SAME call so the shell you tested is the shell
that runs.** The tell that you have already done it is that ordinary utilities vanish
— here `head` reported `command not found` in the same pipeline, which I read as a
typo in the pipeline rather than as evidence that `PATH` was destroyed. **A
`command not found` for a coreutil is never a local problem; it is a statement about
`PATH`, and anything else in that call ran under the same broken environment.**
