## A "PROVEN" DOCSTRING HEADER SITTING ON AN UNRELATED `sorry` LEAF IS THE FOSSIL OF A LOST PROOF — AND IT POINTS AT WHERE THE INPUTS ARE REACHABLE
(2026-08-02, `flt-lean-42`, closing `finite_antiInvariant_jacobian_chabautySemiprimeLevel`
The class-7 sections above treat a mis-attached docstring as *damage to be
repaired*. It is also **evidence**, and it is the cheapest route-finding signal in
this tree.
`exists_cuspidalAbelianSievePrime_oneSixtyNine` — a `sorry` leaf about the **169**
abelian sieve — carried as its header the first paragraph of a **65, 91** leaf's
docstring: *"**… is finite at `65` and `91`** (PROVEN 2026-07-31 over the block
above)"*. Two levels, two subjects, one header. A merge had dropped a declaration
and kept its docstring, splicing it onto the next one.
**Read what that implies about POSITION.** Somebody really did prove the `65, 91`
leaf, and they wrote it *there* — 5500 lines below where the leaf is declared —
because that is the only place its inputs were in scope. The phrase "over the
block above" names the block. So the fossil answers, for free, the question the
task actually turns on: **not "what is the route" but "at which LINE does the route
become legal".**
Here that converted the task from Kolyvagin–Logachev to a 758-line relocation. Both
arithmetic inputs of the generic theorem were already PROVEN at both levels;
`_hnew` and `_hL` simply sat below the leaf that needed them. Nothing mathematical
was owed at all.
**So when a leaf resists, grep the file for its own name in OTHER declarations'
docstrings** — not just for call sites:
    grep -n '<leafName>' <the file>      # then READ each hit's enclosing docstring
A hit whose enclosing declaration is a *different* leaf, especially one claiming
`PROVEN`, is a dropped proof, and its position is the answer.
**Corollary, and it is the standing failure this instance repeats: a file's own
recorded lesson gets applied to ONE consumer and not the others.** `X0.lean`
already carried, in bold, *"when a level-generic cut is made from a level-specific
proof, declare the generic statement where the specific one can REACH it, or the
dedup it exists for cannot be taken"* — written after exactly this went wrong for
the `169` corollaries, which were then fixed. The `65, 91` consumer of the same
generic pair was left unreachable, and the note did not propagate because nothing
propagates a note. **When you act on a lesson, grep for every OTHER consumer of the
thing you just fixed.**
### The complement of "a scratch cannot check declaration order"
CLAUDE.md records that the one thing a scratch module structurally cannot check is
DECLARATION ORDER, because it `public import`s the whole target and therefore sees
every declaration. That is the right warning, and it has a useful converse:
**When ORDER is the ONLY thing wrong, the scratch is exactly the right tool — an
olean has no order.** The built olean contains every name whatever its source line,
so a scratch that restates the target under a primed name and gives the intended
proof verifies the *term* — argument order, implicit/strict-implicit binders,
instance resolution — **before** you pay for a 758-line relocation and a 5276-job
build. Measured here: **9.6 s** for a complete check of the proof, against ~35 min
for the build. If the scratch is green, the relocation is the only remaining risk,
and that risk is settled by the multiset receipt rather than by elaboration.
### A pure relocation's `git diff --stat` is meaningless — quote the multiset receipt
Moving 758 lines produced `11353 +++---, 5690 insertions(+), 5663 deletions(-)`.
That is git's LCS realigning a large block, not content change, and it makes a
pure move indistinguishable from a rewrite by eye. The check that discriminates,
and it must be run inside the move script rather than after it:
    assert sorted(new_lines) == sorted(old_lines) and len(new) == len(old)
Then say in the commit that the stat is realignment noise and the multiset is the
receipt — otherwise a merge worker reading `5663 deletions` on a hoist has no way
to tell it from a branch that deleted 5663 lines. Put the move in its OWN commit
with the source range, the destination line and the parent sha, so a conflict is
resolved by RE-APPLYING the move to the merged text instead of by choosing a side.
**And separate the two `sorry` counts as a pair.** The build's
`declaration uses 'sorry'` warning count and a comment-stripped `sorry` TOKEN count
must fall by the SAME amount (here `101 → 100` both ways). Equal deltas are what
rule out an anonymous inner `sorry` having been swapped in for the named one; the
warning count alone cannot see that.
**Finally, report the delta honestly.** A `−1` produced this way closed no theory
gap: Kolyvagin–Logachev, the Atkin–Lehner descent, the Ramanujan-bound numerics and
Mordell–Weil were all already proven. Ordering repair and mathematics are both
worth doing and they are not the same result — a reader who sees only the count
will assume the second.
