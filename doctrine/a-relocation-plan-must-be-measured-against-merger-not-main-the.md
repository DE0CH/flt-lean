## A RELOCATION PLAN MUST BE MEASURED AGAINST `merger`, NOT `main` — THE BLOCK MOVES

(2026-07-31, third consecutive decline of the same relocation.) The section above
says an audit's *absence claims* go stale in the release window. This is the same
mechanism doing something worse to a *plan*: **every coordinate in a relocation
recipe — line ranges, line counts, which steps are still open, how many use sites
need requalifying — describes a tree that no longer exists by the time anyone acts
on it.** And unlike an absence claim, a plan looks actionable, so the next agent
re-derives it from `main` and gets a *different wrong answer* rather than noticing.

`exists_isWeilEigenvalues_galoisField` in `ModularCurve/X0.lean` is proven one
module downstream, so closing it is a move, not a proof. Three agents in two days
each measured that move against `main` and each recorded a different plan:

| measured | block | length | open steps inside | requalify |
|---|---|---|---|---|
| 2026-07-30 vs `85ee56a7` | `Interface.lean:?` | 761 lines | 3 | ~50 sites |
| 2026-07-31 vs `d451d20b` | `:54431–55801` | 1370 lines | 1 of 3 | ~50 sites |
| 2026-07-31 vs `merger` `d4966bac` | `:55244–56742` | 1499 lines | **1**, renamed | **8**, in 7 decls |

Every row was honest and correctly measured. The block doubled in size while
getting *closer* to done, because proving its steps ADDED lines. And the third
row is the only one you can act on: a branch cutting the move from `main` would
delete `exists_riemannRochGrowth_of_isProperSmoothCurve`'s proof — **re-opening a
leaf `merger` had already closed** — which is the "a branch that was right when
dispatched is wrong when it lands" rule, arriving through a *plan* instead of
through a diff.

Two things follow, and the second is the one that keeps being missed:

1. **Measure the source block on `merger`** (`git show merger:<path> > /tmp/x`),
   never on `main`, and stamp the sha into whatever you write down.
2. **The ~50-site figure was an unstripped whole-file `grep`.** The real count was
   8, in 7 named declarations. A relocation's cost is dominated by exactly this
   number, so an inflated one can kill a cheap move on its own — which is close to
   what happened here. Strip comments and attribute hits to enclosing declarations
   before quoting a use-site count, the same discipline the frontier scans use.

Corollary for the decline itself: **a decline recorded on ownership grounds has an
expiry date that nothing writes down**, so say in the docstring which job held the
lock, and re-check `~/.flt-loop/jobs` before inheriting it. Two of these three
declines were on ownership that had already lapsed.

