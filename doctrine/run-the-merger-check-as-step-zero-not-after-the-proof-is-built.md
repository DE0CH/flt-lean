## Run the `merger` check as step ZERO, not after the proof is built

(flt-lean-250, 2026-07-31.) Dispatched at `exists_hilbertClassField_artinIso` and
`exists_surjective_aut_classGroupQuotient`, I read the file, designed a decomposition, and
proved four of its pieces in Lean — *then* ran

    git show merger:<the file> | grep -n <the target name>

and found both targets already PROVEN on `merger`, in a strictly stronger form, over exactly
the decomposition I had just re-derived (an existence-theorem leaf, the Artin iso recovered by
counting, tower-functoriality of the Frobenius, and transfer of `relNormClassSubgroup` along a
`K`-algebra iso). The check is the one this file already prescribes for the release window; it
cost nothing and it worked. It was simply run too late. **Run it, for every declaration a task
prompt names, BEFORE reading the file.** Task prompts are generated from `main`, and `main` is
the frontier as of the last release.

**And when `merger`'s copy of the file is bigger than `main`'s, read `merger`'s.** The useful
output is not only "already proven" but "already DECOMPOSED": the frontier has moved to names
that only that branch knows. Here the sole remaining leaf,
`exists_unramifiedAbelian_card_classGroup_le_finrank`, **does not exist on `main` at all** — so
it emits no `declaration uses 'sorry'` warning in any build of `main`, no source scan can see
it, no ownership record names it, and a queue audit run against `main` would DELETE a task
naming it. A decomposition performed on an unmerged branch is a *sixth* way for open work to be
invisible, and the only instrument that sees it is the merger's copy of the file.

Corollary for verification: checking out `merger`'s version of a file into your own worktree
and building it is cheap (one module, minutes) and tells the merge worker something it does not
otherwise know — that the branch is green, and the exact warning set it lands with.

