## SPLITTING `A ∧ B` INTO `A` AND `A → B`: THE CHECK IS AGAINST THE *WEAKENED* `A`
(2026-07-31, `RelativePicard.lean`, third cut of that day.)
`exists_relPicZeroSubfunctor` carried two classical chapters at once and said so in its own
docstring — the identity component of a group scheme (SGA3 VI_B 3.10) and properness of `Pic⁰`
(BLR 9.4) — with "whoever takes the leaf takes both". They share no machinery, so they split:
one leaf is the old conclusion **minus** `IsProper jstr`, the other takes that entire conclusion
as its hypotheses and returns `IsProper jstr`. The assembly is `obtain` + repackage.
**The trap, and it is not the obvious one.** Splitting a conjunction looks faithfulness-neutral
because each half is implied by the parent. The first half genuinely is. The second half is
`A → B`, and `A` is now WEAKER than the parent's conclusion — so it admits witnesses that the
deleted conjunct used to exclude, and `A → B` must hold for **every one of them**, not for the
intended `J`. Here `J = P`, `incl = id` satisfies the first half's every clause except
geometric connectedness, and `Pic` is not proper: had the connectedness clause not been there,
the properness half would have been FALSE while both halves still "followed from the parent".
So the cut's real cost is one audit paragraph, and it is the only nontrivial thing about the cut:
**enumerate what the deleted conjunct used to exclude, and name the surviving clause that
excludes it now.** Write it on the second half, where its owner reads it. If no surviving clause
does the excluding, the cut is wrong — put the discriminating property back into the first half's
conclusion rather than hoping the second half's owner will notice.
