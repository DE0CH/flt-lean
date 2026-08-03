## A HOIST IS THE HIGHEST-CONFLICT EDIT THERE IS — give the merger a RECEIPT that it is a pure move
(2026-07-31, `flt-lean-76`, closing `birationalOver_affineLine_of_not_injective_aj`.) Some
leaves are not mathematics at all: the theorem already exists in the same file, declared
BELOW its consumer, so the derivation cannot be written. The repair is a relocation, and a
230-line relocation in a file with four other concurrent editors is exactly the edit the
class-7 section above says a merge will split.
Two things make it safe, and both cost seconds.
**1. Prove the move is pure, mechanically, and quote it in the commit message.** A relocation
diff is 50% `-` and 50% `+` and reads like a rewrite; nobody can see by eye that nothing
inside the moved block was also edited. The sorted line multiset can:
    git show HEAD:<path> | sort > /tmp/old.sorted
    sort <path>          > /tmp/new.sorted
    diff /tmp/old.sorted /tmp/new.sorted     # empty => pure move
Empty, with an unchanged line count, means every line still exists exactly once and only the
ORDER changed. **Put the move in its OWN commit**, separate from the proof that consumes it,
with the old and new line ranges and the parent sha in the message — then a conflict is
resolved by RE-APPLYING the move to the merged text, which is the only resolution that cannot
half-land.
**2. Audit the direction words, because the compiler is silent about all of them.** Docstrings
in this development are dense with "`foo` above" / "`bar` below", and a hoist falsifies some of
them in both the moved text and the text that cites it. Grep every mention of each moved name
and check each direction; here exactly two of about a dozen went stale. Also choose the ORDER
of the moved blocks against their own prose — placing `relPicEquiv_sectionIdeal_of_aj_eq`
before `birationalOver_affineLine_of_relPicEquiv_sectionIdeal` kept its self-description
("the shared first half of both degree-`1` Riemann–Roch leaves below") true for free.
And check the close the way CLAUDE.md checks a release, not by reading the diff: X0's
`declaration uses 'sorry'` warnings went 105 → 104 **and** its comment-stripped `sorry` TOKEN
count went 105 → 104. Equal deltas is what rules out an anonymous inner sorry having been
swapped in for the named one.
