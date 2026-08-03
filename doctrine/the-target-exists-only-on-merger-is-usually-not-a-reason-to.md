## "THE TARGET EXISTS ONLY ON `merger`" IS USUALLY NOT A REASON TO DROP THE TASK
(2026-07-31, `flt-lean-97`.) A task prompt said: audit against `main` first, and if the release
carrying the target declarations has not landed, DROP and re-queue. It had not landed — the two
targets and their proven prerequisite existed only on `merger`, mid-release-27 — and dropping it
would have idled a worker for a whole release cycle.
The cheap thing to check instead is **how many `Fermat` imports the target FILE has.** A leaf
file near the top of the tree usually has one or two, and then merger's version of it is very
nearly self-contained relative to `main`. Here `HyperellipticJacobian.lean` (10 522 lines on
merger) imports exactly `GroupTheory.Descent` (identical on both) and `NumberTheory.
ProjectiveHeight` (differs). Taking merger's copy of BOTH onto a main-based branch built green
in one shot; taking only the target file failed with a single `Unknown identifier`, which is
what named the second file. So the recipe is:
    git checkout merger -- <the target file>
    lake build <the module>              # the failures name the other files you need
    git checkout merger -- <those too>   # repeat; it converges in one or two rounds
**Prefer this to the two obvious alternatives.** Basing the branch on `merger` drags in the
whole unreleased release (153 k lines here) and couples you to its fate. Re-inventing the
decomposition on top of `main` guarantees a rival-cut conflict with merger's version of the same
names — exactly the "two complete proofs of one theorem cannot both be carried" case that costs
an author a reconciliation. Taking the file verbatim makes the merge a no-op for the imported
lines and a pure content add for what you prove on top.
Two things to tell the merge worker when you do it: which files you imported wholesale, and that
if it DECLINES that release's payload for those files your branch reintroduces it. And build a
downstream consumer — `grep -rln "import <YourModule>" Fermat/` — because a main-era consumer
against a merger-era dependency is exactly the interface split that class 7 is about. (Here the
one consumer, `MazurTorsion.lean`, was green.)
