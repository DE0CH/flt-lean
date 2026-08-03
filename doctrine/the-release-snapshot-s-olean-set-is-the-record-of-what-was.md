## THE RELEASE SNAPSHOT'S OLEAN SET IS THE RECORD OF WHAT WAS ACTUALLY COMPILED
(2026-08-01, `flt-lean-4`.) A whole class of task prompt says *"module X has NEVER
been compiled since release N"* — the fourth/seventh invisibility classes, a module
sitting behind a red import. Those prompts are written from a build log, and they go
stale the instant a release publishes. **The direct test is one `ls`:**
    ls -la ~/.flt-release-lake/build/lib/lean/<the module path>.olean
An olean there means the last PUBLISHED release elaborated that module, green,
because the snapshot is taken from the build that published. Absence means it was
never reached. This is a *historical* answer that no source scan, no import-closure
walk and no `lake build` of your own tree can give you — they all tell you about
NOW, and the claim you are checking is about THEN.
My task named two modules as never-compiled-since-release-25 and prescribed a
three-part syntax repair for a 41 600-line swallowed comment. Both oleans were in
the snapshot, dated the evening of release 33, and `swallowed.py` reported both
files clean: five held releases had ended and X0's cone had gone green between the
task being written and being dispatched. **Check the snapshot before you repair
anything a prompt describes as broken** — and note the check costs one command
against a repair that would have been a wasted merge conflict against a tree that
had already fixed it another way.
