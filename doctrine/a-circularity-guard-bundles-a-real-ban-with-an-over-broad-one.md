## A CIRCULARITY GUARD BUNDLES A REAL BAN WITH AN OVER-BROAD ONE — AND MODULE ORDER DECIDES WHICH IS WHICH
(2026-08-02, `flt-lean-39`, `Modularity/Patching.lean`,
`cocycleClass_eq_zero_of_eval₁_kerFix_eq_zero`.)  Leaves in this tree carry
CIRCULARITY GUARDS naming the theorems a proof may not go through.  They are
load-bearing and they are written as a LIST, which is exactly how a correct ban and
an incorrect one end up sharing a sentence:
> it must not be discharged through `not_isIrreducible_of_isHardlyRamified_of_five_le`,
> `IsHardlyRamified.mod_three_reducible`, `Family.lean` or anything downstream of
> them — a proof ending in `exfalso` on `hirr` is the circular discharge and is BANNED.
The first name is a genuine ban: it is proven over pillar α (modularity lifting),
which is proven over the very cluster the leaf is in, so using it is circular even
though the module graph permits it.  **The second cannot possibly be circular.**
`IsHardlyRamified.mod_three_reducible` lives in `HardlyRamified/ModThree.lean`, which
`Patching.lean` `public import`s — and **Lean's module order is a hard guarantee about
PROOFS**: nothing in an imported module can depend on anything in the importing one,
today or ever.  Its own route (Fontaine's discriminant bound, Odlyzko) has nothing to
do with patching either.  So the `p = 3` horn was dischargeable all along, and the
leaf's own docstring had recorded the opposite as settled fact — *"at `p = 3` the
hypothesis set is classically EMPTY … and that horn is not available non-circularly"*
— for three days, while the same discharge was being used TWICE elsewhere in the same
file.
**The check is one command per banned name, and it is decidable rather than a matter
of judgement:**
    grep -n 'import .*<the module the banned theorem lives in>' <your module>
If your module imports it (publicly or not), a cycle through it is impossible and the
ban must be justified some other way or dropped.  If it does NOT import it, ask what
the banned theorem is proven OVER — a name in `Modularity/*` or `Family.lean` in its
proof body is the real signal, not its position in a list.
Two riders, both of which decided this case:
* **A partial discharge is not a vacuous discharge.**  Killing `p = 3` by emptiness
  while the real content survives at `p ≥ 5` is honest; killing the whole leaf by
  `exfalso` is the thing the guard exists to stop.  Say which you did, and REWRITE the
  guard to distinguish them rather than deleting it — the next reader will otherwise
  restore the broad version.
* **What the discharge buys is a HYPOTHESIS on the residue.**  Here the residual leaf
  now carries `5 ≤ p`, which is what Wiles' case analysis actually consumes (the `A₅`
  case of Dickson's wild classification is live at `p = 3` and the vanishing is FALSE
  there as an abstract group-cohomological statement).  A leaf that cannot state the
  hypothesis its own citation needs is a leaf nobody can close.
