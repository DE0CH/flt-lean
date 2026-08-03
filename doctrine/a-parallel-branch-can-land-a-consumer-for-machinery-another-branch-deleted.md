# A parallel branch can land a consumer for machinery another branch DELETED — resolve by counting consumers on the MERGED tree, not by restoring

(Release 37, 2026-08-03, `MazurTorsion.lean`.) `flt-lean-249` deleted
`Isogeny.lean`'s 295-line `GaloisTransport` section on 2026-08-02 as
free-floating, with a written audit ("every consumer of this cluster needs orbit
TRANSITIVITY, not stability").  A parallel branch, cut before that deletion,
landed `isCMJInvariantOfRel_algEquiv` — a theorem whose proof consumes the
deleted section's `End.mapRingEquiv`.  The merge produced six `Unknown constant`
errors inside an otherwise-clean file.

The reflex is to restore the deleted section: it was proven, the deletion looks
like the "mistake", and `git show` makes restoration one command.  The reflex is
wrong until you count consumers ON THE MERGED TREE:

    grep -rn '<the stranded theorem>' Fermat/ --include='*.lean'

Here the stranded consumer had NO code consumers of its own — its intended
customer (`minpoly_eq_of_isCMJInvariantOfRel`) had been proven through a
different bridge (`MazurCMForm.minpoly_eq_of_isCMJInvariantOfQuadratic`) that
never cites stability.  So the deleting branch's audit was still exactly right
on the merged tree, and the repair is to EXTEND the deletion one node up
(delete the stranded consumer, tombstone both sites), not to undo it.

Restoring would have re-landed 295 free-floating lines plus a consumerless
theorem — mass that the free-floating policy would force a later agent to
re-delete, with the deletion audit now split across two git epochs.

Rule: when a merge strands a consumer of deliberately-deleted machinery, the
deletion's written audit transfers to the consumer.  Check the consumer's own
consumers; if there are none, the deletion GROWS; if there are real ones, THEY
are the "check that would justify restoring" that a good deletion tombstone
names (flt-lean-249's tombstone names exactly one, and it did not occur).

Same release, same file, the sibling lesson in one line: a hypothesis
STRENGTHENING (`q ≠ N` → `¬ q ∣ N`, 2026-07-30) reaches only the layers its
branch touched; the untouched middle layer from the other branch keeps the weak
form and fails in BOTH directions at once (callers below it now too weak,
callers above it now too strong).  Strengthen the middle to match the
documented direction — the strengthening branch left a ⚠ note saying which way
it went, and the conversion lemma pattern
(`fun h => hqN ((Nat.prime_dvd_prime_iff_eq hq hN).mp h)`) at the file's other
call sites shows how callers with `N.Prime` in scope cross back.
