## REBUILDING queue1: THE DROP TEST IS THREE-WAY, AND THE TWO-WAY VERSION DELETES THE HIGHEST-VALUE TASKS
(2026-08-03, release 34.)  The merge worker is told to "drop tasks whose leaf is
already proven", and the obvious implementation — harvest declaration names from
each task, keep it iff one of them is still on the frontier — is the two-way
split, and it is WRONG in a way that is silent and expensive.  A task that names
NO declaration has nothing to match and is deleted.
Those are exactly the STRUCTURAL tasks: relocations, reconciliations of two
branches that did incompatible things to one declaration, hoists, scanner
controls, "check the gate and stop".  They are the highest-value tasks in the
queue, because they unblock CLUSTERS rather than closing single leaves, and they
are the ones only a merge worker ever writes.  `flt-cycle.py release` ate one on
2026-07-27 (the X0 relocation, then the single biggest blocker on the batch) and
it had to be restored by hand.
**The test has three outcomes, and it needs a set of ALL declaration names in the
tree — not just the frontier:**
    names an OPEN frontier leaf            -> KEEP (leaf task)
    names a declaration, none of them open -> DROP (its leaf is proven)
    names NO declaration at all            -> KEEP (structural)
Building the third bucket costs one 25 000-name scan of `Fermat/` and is what
makes the second bucket safe.  Measured on release 34: 585 queue2 tasks -> 341
leaf + **2 structural** + 115 dropped.  The two-way split would have deleted both
survivors, one of which was "give the remaining release scanners a POSITIVE
CONTROL" — i.e. the task that protects every later release's green verdict.
Two riders.  **Filter the all-declarations set by length** (`len(n) > 6`): short
names like `map`, `comp`, `one` occur in English prose and would classify a
structural task as a proven-leaf task.  And **tokenise unicode-safely** — split on
"not `isalnum()` and not `_ ' .`", NEVER a `À-￿` class, which swallows `⟨⟩←▸`;
this tree's declaration names are full of `ι`, `Ψ`, `₁`, and a naive tokeniser
silently misses them, which pushes real leaf tasks into the "names nothing"
bucket where they look structural.
