## print axioms per declaration

(Cut verbatim out of CLAUDE.md's `THE GOAL: fully formalize Fermat's Last Theorem, no sorry, n` section at the 2026-08-03 doctrine split; nothing reworded.)

**AND THE PER-DECLARATION ANSWER IS `#print axioms`, RUN IN-FILE — a green build
cannot give it to you** (2026-07-31, `HilbertClassFieldNormal.lean`). An agent
arriving at a target needs to know which of three states it is in: open, proven
outright, or proven-but-transitively-tainted. `lake build` distinguishes only the
first from the other two — a module with no `declaration uses 'sorry'` warning is
*direct*-clean and says nothing about the cone — and the fleet has repeatedly
paid a worker to rediscover the difference.

**CORRECTED 2026-07-31 (`flt-lean-135`): `#print axioms` DOES work from a scratch
module that imports the target, and that is the cheap way to run it — 13 SECONDS
against a 15-to-40-minute re-elaboration of the declaring file.** The paragraph
below says it does not, on the grounds that the module system elides imported
proof bodies; that is true of a `module` file WITHOUT `@[expose] public section`,
and every project file here has one, so the bodies are exposed and the traversal
walks them. Measured, with a control to prove the traversal is real rather than
vacuous:

    module
    public import Fermat.FLT.FreyCurve.MazurTorsion
    #print axioms exists_fundamentalCharacter_of_relIndex_localInertiaGroup
    -- => [propext, Classical.choice, Quot.sound]
    #print axioms
      WeierstrassCurve.exists_localInertia_subgroup_relIndex_dvd_twelve_of_padicValRat_j_nonneg
    -- => [propext, sorryAx, Classical.choice, Quot.sound]   -- a KNOWN leaf in the same file

**Always run the control.** A scratch importer that reported everything clean
would be indistinguishable from a traversal that found nothing, and that is the
failure the paragraph below was written about; one known-sorried name from the
same file separates the two in the same run. The in-file recipe stays valid and
is the fallback when the target module has no `@[expose] public section` or when
its olean is stale — note the scratch reads the OLEAN, so it answers about the
last BUILD, not about your unsaved edit.

`#print axioms <name>` gives it exactly, but **it must be appended to the END OF
THE FILE THAT DECLARES THE NAME**, not written in a scratch module that imports
it. The module system elides imported proof bodies (`value? = none`, and
`#print axioms <name>` gives it exactly.
**CORRECTED 2026-08-02 (`flt-lean-62`), measured rather than argued: IT WORKS
FROM AN IMPORTER, and that is the form to use.** This paragraph used to say the
command "**must be appended to the END OF THE FILE THAT DECLARES THE NAME**"
because "the module system elides imported proof bodies (`value? = none`, and
`import all` does not help), so from a scratch importer the traversal has nothing
to walk". That is FALSE at this pin. A two-line scratch that `public import`s the
module and `#print axioms`es five of its declarations returned
`[propext, Classical.choice, Quot.sound]` for all five **in 7 seconds**, against
the ~50 minutes one `lake env lean` of `ModThree.lean` costs — a 400× difference,
and the difference between running the check and skipping it. So:

    module
    public import Fermat.FLT.Path.To.Module
    @[expose] public section
    #print axioms Some.Namespace.someDecl

**The one precondition is that the module's `.olean` is CURRENT** — the traversal
reads the compiled environment, so a stale or missing olean is what makes the
importer form fail, and that is the likeliest origin of the older claim. Build the
module first (you were going to anyway) and the check is free afterwards. The
append-to-the-declaring-file form below still works and is what to fall back on if
the importer form ever returns nothing:

    cp F.lean /tmp/orig.lean
    printf '\n#print axioms Some.Decl\n' >> F.lean
    lake env lean F.lean            # `[propext, Classical.choice, Quot.sound]` = finished
    cp /tmp/orig.lean F.lean

Here it separated four declarations in one run that a build reported identically:
`conj_unramifiedAbelian` and `sup_unramifiedAbelian` came back axiom-clean, while
`exists_hilbertClassField_normal_over_rat` came back `sorryAx` — and the same
output **names the blocking DIRECTION for free**, since the only paths out led
into `UnramifiedClassFieldExistence.lean` and `ArtinSymbol.lean`.

**But the direction is all it gives you — do not queue the named leaves without
re-checking them against `merger`.** `#print axioms` is evaluated against YOUR
import cone, which is `main`, and `main` is the frontier as of the last release.
Measured the same afternoon: the cluster this audit pointed at had four open
leaves on `main` and three on `merger`, because Chebotarev (`closure_frobAt_eq_top`)
and `exists_hilbertClassField_artinIso` were both already proven and merely
sitting in the release window. So the audit is authoritative about *your* target
and merely indicative about everyone else's; pair it with
`git show merger:<file>` before writing a queue entry, or you will pay someone to
prove Chebotarev a second time.

Two corollaries. Record the verdict in the file's module docstring, because it is
the only place the next frontier scan will look and the only thing that stops the
same target being re-dispatched off the transitive census. And note the reverse
reading: `sorryAx` on your target is **not** a failure when every path to it
leaves your file — say so, name the upstream leaves, and do not go prove them.

**Small trap that cost one wasted build: `lake` is NOT on `PATH` in a worker
shell**, even when you are already logged in to the owning host and never touch
`ssh`. The first invocation returns `lake: command not found` / `EXIT=127`, which
reads like a broken worktree rather than a missing environment. Prefix every
command with `export PATH="$HOME/.elan/bin:$PATH"`. The existing note about this
is filed under *ssh* builds; the cause is the login shell not sourcing elan, so
it bites local runs identically.

