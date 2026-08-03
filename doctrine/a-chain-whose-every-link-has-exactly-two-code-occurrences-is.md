## A CHAIN WHOSE EVERY LINK HAS EXACTLY *TWO* CODE OCCURRENCES IS ONE THREAD — READ ITS EXIT DEFINITION FOR RE-EXISTENTIALIZATION
(2026-08-02, `flt-lean-30`, on the split Hilbert–Blumenthal chain in
`Modularity/MoretBailly.lean`.) The standing consumer check asks *does anything use
my leaf* and stops at one hop. Run it on the WHOLE CHAIN instead, and read the
count itself as the signal:
    exists_splitHilbertBlumenthalCocycle_of_standardLevelModule   2
    exists_splitHilbertBlumenthalFamily_of_standardLevelModule    2
    exists_splitHilbertBlumenthalModuli_of_standardLevelModule    2
    exists_splitHilbertBlumenthalModuli                           2
Comment-stripped CODE occurrences, declaration site included. **Exactly two means
exactly one call site**, so four such theorems in a row are a single thread with one
exit — and then the only question worth asking is what the EXIT does with the
parameters the thread is carrying. Here the exit is
`HasSplitHilbertBlumenthalModuli`, which binds `ρ₀, ρ₀p, Λ, Λp` **existentially**,
and the top of the thread manufactures them from `exists_standardLevelModule`. So
the "for the PRESCRIBED level module and pairing" strength that every link of the
chain carries, and that an entire open leaf
(`hasSplitHilbertBlumenthalCocycleModel_of_levelTwistCocycle`) exists to supply, is
consumed by NOBODY.
**This is invisible to every instrument.** Each link is honestly stated and honestly
proven; no leaf is dead (each has its one consumer); no statement is duplicated; the
build is green. Only the chain read END TO END shows it, and the cheap way in is the
occurrence count, not the mathematics.
Three riders, each of which cost something here:
* **Check the exit's re-existentialization against what DOWNSTREAM actually matches
  on.** The obvious worry is that some later step needs `Λ` to be a particular
  pairing (the Weil pairing of `ρbar`). It does not: the downstream twist matches
  `ρbar` against `ρ₀` through DETERMINANTS
  (`det_eq_cycCharModN_of_isStandardLevelModule`, then
  `twistUnit_mem_specialUnits`), and `SplitModuliLevelAction`'s own docstring says
  `Λ` does not appear in it — `specialUnits` is the isometry group of a balanced
  alternating form on a two-dimensional space whatever the form is. **Grep for what
  the downstream step matches ON, not for what it mentions.**
* **DO NOT ACT ON IT WITHOUT THE OWNERSHIP CHECK.** Collapsing the chain deletes the
  leaf that supplies the unconsumed strength. Here that leaf had a live owner
  (`flt-lean-302`, dispatched at it within one second of me), so the collapse was
  QUEUED and the finding written into the docstring instead. `jobs/*.prompt`'s
  `TARGET:` line is the check, and it takes one `grep`.
* **The collapse also orphans whatever was proven to serve the deleted leaf** — here
  a ~120-line `section LevelTwist` of proven group theory whose only consumer is that
  leaf's call site. Say so when queueing it, or the next agent lands a green commit
  with a block of free-floating code in it.
