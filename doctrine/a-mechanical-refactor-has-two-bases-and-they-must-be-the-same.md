## A MECHANICAL REFACTOR HAS TWO BASES, AND THEY MUST BE THE SAME ONE
(2026-07-31, `flt-lean-98`, dispatched to relocate ~5 300 lines inside `X0.lean` and hoist
~13 000 out of `MazurTorsion.lean`.) A refactor needs a base it can be **verified** on — one
where `lake build` is green — and a base it can be **merged** into — the one the merge worker
will actually be holding. Nothing guarantees those are the same tree, and when they are not,
the refactor is blocked no matter how good it is.
They were not, this day, and both halves failed in opposite directions:
* **`main` was 868 commits behind `merger`**, and `X0.lean` differed between them by
  `+43 356 / −17 099` lines (81 530 → 107 787). A block relocation expressed as
  "delete lines 18483–23815, insert after 63677" names coordinates that do not exist on the
  other side. Unmergeable, whatever its merit.
* **`merger`'s `X0.lean` did not build** — release 27 was deliberately not published because of
  it (`tools/merge/RELEASE-27-HANDOVER.md`: ~193 errors, 8 of them parse errors, not built since
  release 25). So the one base the diff could land on was also the one base it could not be
  verified on.
Verified-only-where-it-cannot-land, landable-only-where-it-cannot-be-verified. **Check both
before starting; it is two commands** — `git rev-list --count main..merger` and
`git diff --stat main merger -- <the file>` — and they cost seconds against hours.
Corollary already discovered independently and worth stating as doctrine: when a large move
must happen anyway, **ship the TRANSFORM, not the diff**. `flt-hoist-genusone.py` (added to
`main` by this branch; it existed only on `merger`, invisible to dispatch, which audits against
`main`) matches every anchor by CONTENT, asserts each unique, and RECOMPUTES the declaration set
from source on each run, so it replays onto whatever base is current and picks up work that
landed inside the moved blocks meanwhile. `flt-lean-123`'s hand-made version of the same edit
was CORRECT and was declined at release 22 purely on conflict volume.
