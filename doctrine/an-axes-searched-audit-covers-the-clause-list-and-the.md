## AN "AXES SEARCHED" AUDIT COVERS THE CLAUSE LIST AND THE HYPOTHESIS LIST — A QUANTIFIER *INSIDE* A CLAUSE IS A THIRD AXIS, INVISIBLE TO BOTH
(2026-08-02, `flt-lean-96`, on `blggt_threeadicHardlyRamifiedMember_of_witness`
in `Modularity/KhareWintenberger.lean`.) That leaf carried the most thorough
atomicity audit in the tree — six numbered axes, each with the check that would
refute it, corroborated independently four times from `Modularity/Interface.lean`.
**All six re-ran and held.** The verdict is correct; what is worth recording is
the axis the shape of such an audit cannot reach.
An `AXES SEARCHED` list enumerates ways to move a CLAUSE out of the conclusion or
a HYPOTHESIS out of the binder list. Neither question looks INSIDE a clause. Here
clause (2) was `∀ m : ℕ, 1 ≤ m → …HasFlatProlongationAt (A ⧸ (3 ^ m))`, and its
own quantifier is a cut candidate that no numbered axis mentioned.
**Analyse such a quantifier in BOTH directions; they close for opposite reasons
and only one of them is obvious.**
* *Downward* (level `m + 1` ⟹ level `m`) was TRUE — `A ⧸ (3 ^ m)` is a quotient
  of `A ⧸ (3 ^ (m + 1))` and `e = 1 < 2 = p − 1` over `ℤ_3`, so Raynaud applies —
  **and buys nothing**, because no finite set of levels implies a `∀`. A true
  implication that does not shrink the obligation is the commonest false positive
  on this axis; check what it *delivers*, not whether it holds.
* *Upward* (assemble the tower into one object) is the cut you actually want, and
  it is a `p`-divisible group — i.e. it RELOCATES the citation into missing
  theory rather than reducing it.
This is the standing "the quantifier is a cut too" rule one level in: that rule is
about the leaf's OUTER conclusion quantifying over a finite index set, and it does
not fire when the quantifier is a clause's own and ranges over `ℕ`.
### AN ABSENCE CLAIM CAN DRIFT IN THE LETTER WHILE HOLDING IN SUBSTANCE — READ THE NEW HIT'S MATHEMATICS, DO NOT COUNT HITS
Same run, and it is the trap that makes re-running an absence check *look* like
it refuted the audit. That leaf's axis 6 rested on `grep -rn Abrashkin Fermat/`
"returning only two prose mentions". It now returns **five**, which reads as a
refutation — and the new hit is a DIFFERENT THEOREM BY THE SAME AUTHORS:
`ModThree.lean` cites Fontaine/Abrashkin for the `p = 3` *local ramification
estimate* of *Il n'y a pas de variété abélienne sur ℤ*, whereas the axis needs
the *global emptiness* statement ("no irreducible flat `ρbar` unramified outside
`ℓ`"). Substance unchanged; the axis stands.
**So a citation-NAME grep is the wrong instrument for an absence claim**, because
a working mathematician is cited for several theorems and this tree cites the
nearest one constantly. Grep for the STATEMENT shape, and when a count moves,
open the new hit and read what it proves before recording either a refutation or
a confirmation. The same run found `RamificationFiltration` present
(`ArtinConductor.lean`) against an audit that called the higher-ramification
filtration absent — also a letter-level drift, since that structure is
deliberately axiomatised only at Herbrand values and is not the ramification
theory Fontaine–Laffaille needs. Two drifts, zero substance, and both would have
read as refutations to a hit-counter.
Corollary worth its own line: **the two theories that actually gate such a leaf
should be re-checked in all THREE trees** — `Fermat/`, `~/cs/FLT/FLT` and the
mathlib pin. Here `p`-divisible groups and `B_cris`/Fontaine–Laffaille came back
empty in all three, which is what makes the verdict a fact rather than an
inherited claim.
