## A DECLARATION-ORDER LEAF CLOSES BY MOVING, NOT BY PROVING — READ THE DOCSTRING FIRST

(2026-07-31, `MazurTorsion.lean`, third instance in this file alone.) Some leaves contain
no mathematics at all. Every input is already PROVEN — one of them just happens to be
declared FURTHER DOWN THE SAME FILE, and Lean has no forward references, so the leaf was
cut in a combined form to dodge the ordering. `A₀-1`
(`exists_mem_localInertiaGroup_cyclotomicCharacterModL_eq`) closed this way on 2026-07-28;
`A₀-3a-i-b` (`det_galoisRep_five_eq_one_of_mem_localInertiaGroup`) closed this way on
2026-07-31 over a 234-line hoist and **fourteen lines of vocabulary glue**, having been
cut the previous day as a "Silverman *AEC* III.8.3 and the Weil pairing" leaf.

**The tell is in the leaf's own docstring**, and this development writes it down every
time: *"is ALREADY PROVEN IN THIS FILE"*, *"declared FURTHER DOWN"*, *"which is the only
reason this leaf is stated in the combined form"*, *"a prover has two honest routes:
hoist …"*. So the first action on any leaf is to read its docstring for that sentence,
and the second is `grep -n` the named declaration — if it exists below you, the leaf is
GLUE and the citation in its header is decoration.

**A hoist is safe exactly when four things hold, and all four are one grep each:**

1. *Namespace*: the source and destination sites are under the same `namespace`/`section`
   (`grep -n '^namespace \|^end \|^section '` and read off the enclosing block). An
   `open X in` binds only the next declaration and does not count.
2. *No backward dependency*: nothing the moved block cites is declared BETWEEN the two
   sites. Resolve each cited name — external (imported) is free, in-file must be above
   the destination.
3. *No stranded consumer*: every consumer of the moved names is BELOW the destination.
   `grep -n '<name>'` over the file; consumers far below are unaffected by definition.
4. *The move is verbatim*. Do it as a line-range relocation guarded by ASSERTIONS on the
   first and last line of the block and on the two lines straddling the insertion point —
   a 234-line block cannot be retyped safely, and `git diff --stat` reading
   `N insertions(+), N deletions(-)` with equal `N` is the receipt that nothing was
   dropped. (Anything else and you have hit class six from the other direction.)

**Do NOT restate the downstream half as a new leaf** to avoid the move. That manufactures
a duplicate cut — invisible to every sorry scan, and it makes the frontier count go UP
while pretending to go down.

**And do not assume the rejection of one hoist rejects yours.** The same file records that
release 12 REJECTED hoisting `WeierstrassCurve.PotentiallyGoodModel` and deleted the file
that did it; that verdict is about a structure with a ~1500-line existence chain and says
nothing about a self-contained two-theorem block. Judge the block you actually have.

**A hoist verified by all four checks can still not COMPILE, and the reason is the next
section.** `det_galoisRep_five_eq_one_of_mem_localInertiaGroup` was hoisted correctly —
namespace clean, no backward dependency, no stranded consumer, block byte-identical — and
the fourteen lines of glue on top of it were red. The four checks are about the MOVE. They
say nothing about the glue, and only a build does.

