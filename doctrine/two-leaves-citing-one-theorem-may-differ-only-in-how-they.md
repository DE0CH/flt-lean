## TWO LEAVES CITING ONE THEOREM MAY DIFFER ONLY IN HOW THEY PRESENT A PARAMETER — FUSE BY QUANTIFYING OVER THE PRESENTATION
(2026-08-02, `flt-lean-307`, `FreyCurve/MazurTorsion.lean`, direct sorries `2 → 1`.)
This file already records how to FIND a duplicated citation ("TWO LEAVES CAN CITE THE
SAME THEOREM WITH NO NAME, STATEMENT OR TYPE IN COMMON") and what to do when one leaf
implies the other. It does not cover the commonest hard case: **the two leaves are
genuinely non-identifiable — neither is a special case of the other — and a correct
note in the file says so.** Then "delete the duplicate" is wrong, and the file really
does owe one citation twice.
The instance. The first main theorem of complex multiplication — irreducibility over
`ℚ` of the class polynomial of an imaginary quadratic ORDER — was stated twice, over
two presentations of the order:
* `IsCMJInvariant n`      : `End W = ℤ[ψ]`, `ψ² = [−n]`,      discriminant `−4n`, never ODD;
* `IsCMJInvariantOfRel m` : `End W = ℤ[φ]`, `φ² − φ + m = 0`, discriminant `1 − 4m`, never EVEN.
Neither presentation reaches the other's discriminants, so the two predicates must not
be identified, exactly as that file's subsection note says. **The repair is to quantify
over the PRESENTATION**: `φ² + bφ + c = 0` with `b * b < 4 * c`. Both old leaves are
then instances (`(b,c) = (0,n)` and `(−1,m)`), both become two-line theorems, and the
tree owes the citation once. The bridges are pure cast arithmetic and the whole thing
verified in **two scratch rounds at 10 s each**.
**THE CHECK THAT MAKES A FUSION FAITHFUL, and it is the only real work: the new
parameter must range EXACTLY over the intended objects.** Here `b * b < 4 * c` says the
discriminant `D = b² − 4c` is negative, and `D ≡ b² ≡ 0, 1 (mod 4)` holds automatically,
so `(b, c)` hits every imaginary quadratic discriminant and nothing else (`D ≡ 0`:
`b = 0`; `D ≡ 1`: `b = 1`). So every instance of the fused leaf is the same citation for
one order and no instance demands anything new. **If the parametrisation OVERSHOOTS you
have manufactured a harder — possibly false — leaf while every count says you removed
one.** Compute the image of the constraint before writing the statement.
**And re-running the falsity audit after a fusion is cheap in a specific way: check that
the fused hypothesis SPECIALISES to each old one on the nose.** `hn : 0 < n` is
`0 * 0 < 4 * n`; `hm : 0 < 4 * m − 1` is `(−1) * (−1) < 4 * m`. When it does, both old
witnesses transfer verbatim as the two instantiations and there is nothing further to
verify — record them that way in the new docstring rather than writing "inherited".
**THE DUPLICATION HAD ALREADY BEEN FOUND, AND THE RECORD WAS IN A COMMIT MESSAGE ON AN
UNMERGED BRANCH.** `flt-lean-179` (4 commits, not in `~/.flt-merge-batch`, not an
ancestor of `main`) had diagnosed exactly this pair, named it as CLAUDE.md's own
"two leaves citing one theorem" hazard, and written *"only ONE should be dispatched"* —
in `git log`, invisible to every scan of the tree. It also carries a RIVAL repair: it
decomposes the `OfRel` side into `finite_setOf_isCMJInvariantOfRel` +
`ncard_setOf_isCMJInvariantOfRel_le`, which the fusion makes consumerless. So:
* **`grep` the queues and the branch COMMIT MESSAGES, not just the tree, before
  repairing a duplicate** — `~/.flt-loop/queue2` held a 40-line prior analysis of this
  exact question, including a `CHECK BEFORE STARTING` clause naming my target as the
  rival cut, and one `git log --all --grep` would have found the branch;
* the tie-break between two rival repairs of a duplication is CLAUDE.md's standing one,
  *fewer OPEN leaves after*: fusing leaves 1, the rival decomposition leaves 3
  (my target, plus its two).
