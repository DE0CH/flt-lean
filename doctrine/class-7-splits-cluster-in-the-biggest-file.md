# Class-7 splits cluster in the biggest file, and the first error list is a lower bound

(Release 35, 2026-08-03.) A 387-branch batch left `X0.lean` red in SIX
independent kept-one-half-dropped-the-other ways at once: a structure field
whose producers landed without the field (`CyclicSubgroupOfOrder.etale` ×
`nsmul_liesIn`, two branches crossing), a signature whose callers gained an
argument the declaration never did (the KM `hS` chain), a ~550-line stretch
inserted at a bogus anchor 50k lines above its own definitions, three
consumer-before-definition declaration-order splits, one dropped `variable
{k : ℤ}` line (~40 `Unknown identifier k` errors from one lost line), and a
consumer reading a conclusion clause in a form its supplier's tree-copy never
adopted (★ vs ✦). Lessons that generalize:

- **`maxErrors` (100) caps the error list.** The first red build's list is a
  LOWER bound on the damage — errors past the cap, and every module downstream
  of the failing one, are invisible. Budget repair rounds accordingly; do not
  announce a damage census from round 1.
- **Work from the blob catalog, not from `git log -S`.** `git log -S name --
  <giant file>` times out (>2 min); the per-release catalog of unique blobs of
  the file (`ublobs_x0.txt`: one `blob commit` pair per distinct version) makes
  every "which branch has the dropped half" question a `git cat-file blob |
  grep` loop over ~100 blobs, seconds each.
- **Check for a proven rival before moving a misplaced block.** A block
  stranded above its definitions is not automatically the version to keep: in
  release 35 the misplaced Abel chain (`listSum_map_post_eq_*`, one sorry
  leaf) had a PROVEN rival chain (`listSum_post_eq_*`) already consumed at the
  proper site. The repair was deletion (frontier −2), not relocation. Test
  each stranded declaration for consumers OUTSIDE the stranded block first.
- **A dropped-half repair can hide in a consumer, not the supplier.** The
  ★/✦ case: the tree kept the ★-form supplier PROVEN while the consumer used
  the withdrawn ✦ form. When the kept half is proven and implies what the
  consumer needs, derive it inline at the consumer (four lines) instead of
  re-sorrying the supplier in the other form.
- **An "Unknown identifier" burst inside one namespace is a lost `variable`
  or `open` line**, not N separate problems — see also the release-34 lesson
  that a lost scope line reports as a type error.
