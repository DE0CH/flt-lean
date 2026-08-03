## A CUT CAN MANUFACTURE ITS OWN DECLARATION-ORDER LEAF — and an UNDERSCORED BINDER is where the reason hides
(2026-07-31, `flt-lean-178`, `hasInertiaLevelOneFlag_quotient_cornerIdeal` in
`HardlyRamified/Family.lean`.  Two leaves closed, no mathematics done.)
The declaration-order sections above all describe the same history: a theorem was
proven LATER, further down the file, and a leaf cut earlier cannot reach it.  There
is a sharper and commoner variant that those sections do not cover, because it needs
no elapsed time at all: **a single agent, in one session, cuts a leaf ABOVE the
machinery it writes to prove it.**  Here the leaf was cut out of its consumer, the
general lemma that discharges it (`hasInertiaLevelOneFlag_of_surjective_bialgHom`) was
written the SAME DAY 320 lines below it, and the leaf was left `sorry` — with a
docstring correctly recording the whole route and correctly recording that "the
mathematics is one paragraph and the difficulty is entirely instance plumbing".
That sentence is the tell, and it is worth grepping for: **a leaf whose own docstring
says the mathematics is a paragraph and the difficulty is plumbing is very often not a
leaf at all.**  Before attacking such a statement, `grep -n '^theorem'` the file and
compare LINE NUMBERS with the machinery its docstring names.  If the machinery is
BELOW, the task is a relocation, not a proof — and moving the leaf DOWN is the cheap
direction, because its consumers are below it already by construction (they are what
it was cut out of).
**THE OTHER HALF, AND IT IS THE PART NOBODY CHECKS: AN UNDERSCORED BINDER WITH A
COMMENT EXPLAINING WHY IT IS UNUSED.**  This leaf's true remaining obstruction — the
hypothesis `habel` — was *already present two levels up*, as `_habel`, being
DISCARDED under a four-line comment:
> `habel` STOPS HERE: the callee was strengthened to derive commutativity of the
> convolution monoid from `hflag` alone, so it no longer takes the hypothesis.
The comment was FALSE, and the refutation is one sentence: any finite `p`-group has a
chief series with order-`p` quotients, so a NONABELIAN one satisfies every clause of
the flag predicate — the flag constrains the lattice of submonoids and says nothing
about commutativity.  So a hypothesis that was in hand, for free, at the call site was
being thrown away one declaration above a leaf that existed *because it lacked exactly
that hypothesis*.
**The check costs one `grep` and it is mechanical rather than mathematical: when a
binder is underscored with a comment saying the callee no longer needs it, read the
CALLEE'S SIGNATURE.**  Here the sibling `hasInertiaLevelOneFlag_of_surjective_bialgHom`
takes `habel` explicitly, in the same file, 130 lines away — which settles it without
any thought about `p`-groups.  A prose claim that a hypothesis became derivable is
exactly as reliable as a prose claim that a leaf is still open (which this file already
tells you to distrust), and it is *less* visible, because an underscore reads as
tidiness rather than as an assertion.
Generalise the pair: **the two cheapest things to check on a stuck leaf are its
POSITION in the file and the UNDERSCORED BINDERS of its consumers.**  Neither is
mathematics, both are one command, and between them they closed a node that three
task-prompt paragraphs had priced as an interface-threading project.
**Rider, from the same file and the same afternoon: the dead twin.**  With the leaf
closed, a comment-stripped tree-wide scan showed the file's remaining "Raynaud" leaf
had a SECOND copy — `isMultiplicativeType_corner_of_connected_of_cornerLevelOneFlag`,
the same citation at a concrete corner instead of an abstract `A` — with exactly one
occurrence in the tree, its own declaration.  Two rival cuts of one citation had both
landed and the consumer had wired itself to the abstract one, so the concrete one had
been an OPEN leaf that was also DEAD since the day it was written.  It is the
abstract theorem instantiated, so it closes in one line.  **Run that scan on the
neighbours of any leaf you close** — a file that has been re-cut twice in a week is
exactly where a duplicate is, the two copies share no identifier, and no `sorry`
count, ownership test or duplicate-NAME scan can see it.
