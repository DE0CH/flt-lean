## THE SAME MATHEMATICS CAN SIT BELOW YOU **AT A DIFFERENT GENERALITY** — that is TWO obstructions, and neither is the one you check for
(2026-08-01, `flt-lean-251`, cutting `neronExtension_of_etale_of_groupSchemeModel`
in `X0.lean`.) The standing checks cover two shapes: *the machinery is
DOWNSTREAM* (in a file that imports yours) and *the machinery is BELOW you*
(declaration order in your own file). There is a third, and it is the one that
wastes a cut: **the machinery is below you AND at an incomparable generality.**
Weil's extension theorem was already in that file — `exists_weilExtension_purity`
(EGA IV₄ 20.4.12), `exists_weilExtension_of_abelianScheme` PROVEN over it — some
2500 lines BELOW the target. Both readings a grep invites are wrong:
* *"already cut, nothing to do"* — false. That development is for a smooth
  PROPER CURVE mapping to an ABELIAN scheme; the target needs an arbitrary
  smooth scheme mapping to a smooth separated GROUP scheme, which is exactly the
  gap between a Néron model and an abelian scheme. Neither statement implies the
  other;
* *"cite it"* — impossible twice over, by declaration order and by generality.
**So when a grep finds your mathematics elsewhere in the file, compare THREE
things before concluding anything: the line number, the source's generality, and
the target's generality.** A hit that fails any of the three is not a hit.
**And when the other copy has a LIVE OWNER, record the consolidation instead of
performing it.** The right long-run arrangement here is one purity leaf at the
GENERAL generality, from which both the abelian-scheme case and the group-scheme
case follow — but `exists_weilExtension_purity` was another agent's dispatched
target, and restating or retiring somebody's live target is not a passer-by's
call. Put the consolidation in the new leaf's docstring WITH the reason it was
declined and the condition that reverses it (here: both leaves landed, one owner
holds them), and put it in `to_merger`. A decision recorded is reversible; a
consolidation done under a live owner is a conflict in the largest file in the
tree.
Corollary that fell out of the same grep, and it is the cheapest audit in this
file: **an open leaf whose only comment-stripped occurrence is its own
declaration is DEAD**, and this cluster had one — `exists_localExtension_of_abelianScheme`
was the residue of a losing rival cut (its consumer's docstring still names it,
while that consumer's `by` block calls the winner), together with two PROVEN and
equally consumerless helpers. An agent was dispatched at it the same day. Run the
consumer scan over EVERY open leaf in the neighbourhood you are about to touch,
not just your own.
### `X0.lean` ELABORATES IN ~250 SECONDS, NOT 25 MINUTES — re-measure before planning around a quoted cost
Several sections of this file price one `lake env lean` of `X0.lean` at 8, 25 or
40 minutes and tell you to plan the whole run around avoiding it. Measured
2026-08-01 on `quicksilver`, with `/usr/bin/time` and a `.lake/build` rsynced
from `~/.flt-release-lake`: **`WALL=249.88` for 118 982 lines, `EXIT=0`.** A
scratch module `public import`ing the built `X0.olean` was **7 seconds**.
So the real budget is a 7-second inner loop and a 4-minute final verify, and an
agent that plans for a 40-minute verify will do noticeably less work than it
could. Two conditions make the measurement what it is, and both are cheap to
reproduce: the artifacts must be seeded rather than built (`git diff --stat
$(cat ~/.flt-release-lake/sha) HEAD -- Fermat/` empty, then `rsync -a --delete
~/.flt-release-lake/build/ .lake/build/`, 91 s), and `lake env lean` must be used
rather than `lake build` — the latter deletes the target olean and takes the
scratch loop down with it for its whole duration.
**The general rule is the one this file already applies to leaf costs and to
absence claims, and it applies to ITS OWN numbers: a quoted elaboration time is a
measurement of one file on one day, and these files grow and these machines
change.** `/usr/bin/time -f WALL=%e` costs nothing; run it once at the start and
plan on the answer.
