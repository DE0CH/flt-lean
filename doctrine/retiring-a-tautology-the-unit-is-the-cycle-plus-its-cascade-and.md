## RETIRING A TAUTOLOGY: THE UNIT IS THE CYCLE **PLUS ITS CASCADE**, AND THE CASCADE IS THE DECISION
(2026-08-01, `flt-lean-140`, `FreyCurve/MazurTorsion.lean`. Task said "delete the
five"; the honest deletion was **28 declarations, 1487 lines**.)
A tautology forms here in a specific, recurring way, and it is nobody's mistake: leaf
`L` is proven the long way round through a tower; later somebody proves `L'` — the
SAME statement — cheaply, upstream; and the tower's bottom step is then re-pointed at
`L'`. Now the tower derives `L` from `L'`, and `L ≡ L'`. Every declaration in it is
true, proven, and green, and the file has stopped asserting anything with them.
**Three things about executing the retirement, each of which changes the answer.**
**1. RE-DERIVE THE CYCLE — it is usually longer than the prompt says, and it usually
has TWO duplicate pairs, not one.** My prompt named a five-declaration chain from
`exists_endMinpoly_of_stable_cyclic_mazurLevel` down to
`nonempty_isCMByRamifiedMaximalOrder_geomPoint_mazurLevel`. The real loop closed one
link higher, at `nonempty_isCMByRamifiedMaximalOrder_of_classify_eq` — so the tower ran
between **two** pairs of character-identical statements
(`_mazurLevel` ≡ `_isolatedJ` at the top, `geomPoint` ≡ `_of_classify_eq` at the
bottom), and the honest cut deletes six declarations rather than five-plus-a-one-liner.
**Do not "keep the name and make it `exact <the twin>`".** That is the tautology with
fewer lines, and it is exactly what `tools/merge/dupstmt.py` exists to flag. Delete the
duplicate and re-point its one consumer; keep the copy the file's remaining route can
reach.
**2. THE CASCADE IS COMPUTED, NOT EYEBALLED, AND IT DOMINATES.** Six cycle declarations
orphaned **22 more** — a whole `namespace` of `ψ = √−N`-as-a-morphism plumbing plus two
genuinely reusable LEVEL-GENERIC theorems. Compute it as a fixpoint over the
comment-stripped, dot-suffix-aware usage graph ("no surviving consumer ⇒ dead"),
iterate to convergence, and then **grep every dead name over the whole tree and require
ZERO code hits** before deleting anything.
Two traps in that scan, both of which I hit:
* **dot notation.** `E.exists_isogenySignature` does not contain the token
  `exists_isogenySignature`. Index every dotted SUFFIX of every token, or the scan
  reports "(no code occurrences anywhere)" for declarations with four live consumers —
  and you will delete them. My first run said exactly that about the entire Serre
  isogeny-signature analysis.
* **the fixpoint under-reports at its own edges.** A declaration consumed only by
  something that is *itself* consumerless is never even a candidate, because nothing
  dead mentions it. Here `phiHom`/`phiHom_apply` survived round 6 and were dead;
  re-seeding with them took 26 → 28 and emptied the namespace exactly.
**3. DECIDE THE CASCADE DELIBERATELY — the free-floating rule is what settles it.**
This is the one place judgement enters, and CLAUDE.md pulls both ways: the
refutation-cascade note warns that over-deletion once removed 17 clean theorems that
were consumerless only *because of the deletion*, while the free-floating rule forbids
leaving consumerless declarations at all. **The discriminator is whether an alternative
cut point exists.** There, one did — cutting at the lowest *poisoned* statement kept the
clean ones consumed. Here the tower is a single linear chain with one entry and one
exit, so no cut preserves anything; the cascade is genuine and it all goes. Say so, and
say what was lost: two of mine (*a CM datum for `𝒪_{−N}` is `N`-isogenous to itself*,
*a self-`N`-isogenous `ℚ̄`-moduli point is `w_N`-fixed*) were level-generic and proven,
and are worth one `git show` to restore the moment anything wants them.
**AND CHECK WHAT THE TOWER'S BODIES USED, SEPARATELY FROM THE TOWER.** The deleted
`_mazurLevel`'s body was the only *visible* consumer of Serre's signature analysis
(`exists_isogenyCharacter`, `exists_isogenySignature`,
`not_isogenyCharacter_of_isogenySignature_ne_six`,
`mem_classNumberOnePrimes_of_isogenySignature_six`,
`potentiallyGoodReduction_of_isogenyCharacter`). It was not the only one — all five are
consumed by `not_isogenyCharacter_of_prime_ge_twentyThree` and by `X0.lean`'s
`false_of_stable_of_forall_padicValRat_nonneg`. That check is the difference between
deleting an assembly layer and deleting a theory, and it is one scan.
### The bookkeeping, because none of it shows in any count
**The frontier does not move and must be reported as not moving.** Every declaration
deleted was PROVEN; no `sorry` was added or removed. A −1487-line diff with an unchanged
warning set is otherwise indistinguishable from vandalism, so the commit has to say what
the file stopped asserting.
**Write the deletion record AT the deletion site, with the recovery command and the
parent sha.** `git show <parent>:<path>` plus the line range is the whole cost of
restoring proven mathematics, and it is unfindable six months later without it. Then
sweep the file for prose naming the deleted declarations and mark those paragraphs
WITHDRAWN rather than deleting them — the mathematics in them is correct and is the only
record of what the retired route was.
**A neighbouring queued task may be discharged for free by choosing the right cut.** A
separate task asked to widen `exists_gamma0Datum_descent_mazurLevel`'s conclusion to kill
a ~20-line duplicated `hinv` derivation. That duplicate lived inside the body of a
declaration this deletion removes, so it went with it — no signature change, no call-site
churn. **Before performing a queued refactor, check whether the deletion you are already
making deletes its subject.**
**Do not edit a giant upstream module for PROSE.** Four stale cross-references to deleted
names survive in `X0.lean`. Touching that file rebuilds the largest cone in the tree
(hours) and lands a conflict in the hottest file in the repository, to fix comments. That
belongs in `to_merger` and in the next edit that has a real reason to open the file.
