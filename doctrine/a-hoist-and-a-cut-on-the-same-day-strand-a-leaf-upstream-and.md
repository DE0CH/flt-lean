## A HOIST AND A CUT ON THE SAME DAY STRAND A LEAF UPSTREAM AND ITS PROOF DOWNSTREAM
(2026-08-02, `flt-lean-94`, closing `X0GenusOne.exists_x0Compactification_relPoint_equiv_point`
— a leaf three audits had priced at "an explicit plane model of `X_0(N)`, i.e. the classical
identification of the genus-one modular curves with the elliptic curves `N a 1`; neither
exists at this pin".  It was a **declaration-order leaf**, and the proof is six steps over
declarations already cited from the same file above it.)
The mechanism needs two agents, one day, and no mistake by either:
* **flt-lean-28 HOISTED** the whole `X0GenusOne` namespace out of `FreyCurve/MazurTorsion.lean`
  UP into `ModularCurve/X0.lean`, so that a theorem 40 000 lines above could cite it.  The leaf
  travelled up with it.
* **flt-lean-170 CUT** the leaf's arithmetic out as `card_relPoint_of_modelTable` and PROVED it
  — in `MazurTorsion.lean`, where the leaf had lived that morning and where its own consumer was.
Both landed.  The leaf is now UPSTREAM and its proof is DOWNSTREAM, in a module that
`public import`s it, so the leaf cannot cite the theorem that closes it and **nothing in the
tree says so**.  The downstream module's docstring even records the key fact — *"it is
`Fermat.card_relPoint_x0_eichlerShimura`, PROVEN in `X0.lean` upstream"* — and correctly
retires the leaf's cost estimate; it simply never asks whether the leaf it was cut FROM is
upstream too.
**Every instrument reports ordinary open work.**  The leaf emits its `declaration uses 'sorry'`
warning; it has a live consumer (`nonempty_relPoint_equiv_modelPoint`, so it is not dead); its
own docstring is long, dated, re-audited and *wrong*; and the machinery that closes it shares no
identifier with anything the leaf mentions.
**THE DETECTOR IS ONE GREP, AND IT IS NOT A GREP FOR CODE.**  Grep your target's NAME across the
tree and read the PROSE hits in files that import yours:
    grep -rn '<yourTargetName>' --include=*.lean Fermat/ | grep -v '<your file>:'
Downstream docstrings that say *"cut out of `<yourTarget>` as item (i)/(ii) of that leaf's own
analysis"* are telling you that somebody already did your task, one module too low.  Six of the
eight hits here said exactly that.  A grep for CODE consumers answers a different question
(is the leaf dead?) and returns nothing useful.
**Then check whether the downstream proof is upstream-expressible, name by name.**  It usually is,
because a cut made downstream normally consumes only what the leaf itself could see.  Here all
four ingredients were in `X0.lean` at lines 65099, 67653, 67988 and 68486 — every one of them
ALREADY CITED from `X0.lean` above the leaf's own line (69171, 69185, 69247, 85006, 102398,
102861).  That last check is what makes the accounting airtight: **the proof adds no new `sorryAx`
edge at all**, because every constant it names was already in the file's cone above it.
**LAND IT AS AN INLINE, NOT AS A HOIST — and queue the hoist separately.**  The tidy repair is to
move the four downstream declarations up and delete them from the importer.  Do not do that in the
same commit as the proof: `semmerge.py` propagates ADDITIONS and never DELETIONS, so a dropped
deletion is a hard `has already been declared` in the two hottest files in the tree, and CLAUDE.md
already records that exact failure at 249-declaration scale.  Inlining their content into the
leaf's own body touches **one declaration in one file**, cannot collide with a concurrent editor
of either, and yields the receipt below.  Completing somebody else's hoist is a pure relocation and
belongs in its own commit.
**The receipt for "a clean −1 with no new leaf" is two numbers, and both are cheap:**
    git diff <file> | grep -E '^[+-] *sorry *$'      # exactly one `-  sorry`, zero `+  sorry`
    <comment-stripped `sorry` token count>            # 101 -> 100, matching the build's warning set
A `−1 +1` delta is indistinguishable from one closure plus one unrelated disclosure; the token
count keyed against the compiler's warning set is what tells them apart.
**Generalisable, and it is the sharpest form of "missing machinery may be DOWNSTREAM":** when a
leaf's docstring names a large classical citation and the leaf has recently MOVED between modules,
suspect that its proof moved the other way.  A relocation and a decomposition performed on the same
node on the same day are individually correct and jointly leave the node unclosable — and the
frontier records it, truthfully, as a chapter of missing mathematics.
