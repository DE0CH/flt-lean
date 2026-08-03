## A PROMPT'S "THIS WAS HOISTED ABOVE YOUR LEAF" IS A CLAIM ABOUT LINE NUMBERS — `grep -n` IT

(2026-08-01, `flt-lean-205`, on `exists_stepanovJetLinearForms_of_frobeniusSplit`
in `MoretBailly.lean`.) The task brief listed, in bold, the machinery "ALSO HOISTED
TO JUST ABOVE THE LEAF on 2026-07-31, so you can use all of it", ending with
"and crucially `stepanov_exists_wd_rem`". `stepanov_exists_wd_rem` is at line
19235 and the leaf is at 17169 — **on `main` AND on `merger`**, i.e. the hoist was
planned, written into a docstring, and never performed. Lean has no forward
references, so the single most load-bearing input the brief promised was not usable.

The existing rules cover a name that is ABSENT (stale worktree, unmerged branch,
declined merge). This is a fourth cause of the same feeling, and the cheapest to
check because it needs no git at all:

    grep -n 'theorem <the promised name>\|theorem <your leaf>' <the file>   # compare!

**A promise about POSITION is exactly as perishable as a promise about existence,
and much easier to believe**, because the name really is there and the grep that
finds it looks like a confirmation. Run the check on every declaration a brief
says you may use, before planning around it — one `grep -n` for the pair, and read
the two numbers.

Corollary for whoever writes such a brief: a hoist is not done until the block has
MOVED. Saying "X should be hoisted" in a docstring and "X has been hoisted" in a
prompt are one keystroke apart and a whole task apart.

### Two things this task turned up that are worth reusing

**A missing classical difference quotient is a `divByMonic` away, not a geometric
sum.** `e₂`, defined by `F(X,Y) − F(X,Y') = (Y − Y')·e₂`, had existed only in PROSE
in three docstrings of that file. The obvious construction is Schmidt's own —
`∑_n c_n ∑_{s+t=n−1} Y^s Y'^t` via `geom_sum₂_mul` — and then monicity and degree
are coefficient computations. Building it instead as
`(F with Y renamed to the outer variable) /ₘ (Y' − Y)` makes all four facts short:
the defining identity is `Polynomial.modByMonic_add_div` plus
`Polynomial.modByMonic_X_sub_C_eq_C_eval` (the remainder IS `F(X,Y)`, because
substituting `Y` back for `Y'` recovers `F`), the degree is
`Polynomial.natDegree_divByMonic`, and monicity is
`Polynomial.leadingCoeff_divByMonic_of_monic` — **which is the lemma to know: it
says division by a monic does not change the leading coefficient, so a monic
divided by a monic of smaller degree is monic, and mathlib has no
`Monic.divByMonic` to grep for.** Whole construction plus the four facts: ~45 lines.
Same recipe applies to any `(f(a) − f(b))/(a − b)` this development needs.

**`rw [map_sub]` can fail on a term that visibly matches while `rw [← map_sub]`
succeeds on the same goal.** Observed with a `RingHom` between triple-nested
polynomial rings: the error is the standard *"Did not find an occurrence of the
pattern `?f (?a - ?b)`"* printed against a target containing exactly that, and
`simp only [map_sub]` reports the lemma as an UNUSED simp argument while `map_mul`
in the same call fires. The abstract `example (f : A →+* B) : f (a - b) = f a - f b
:= by rw [map_sub]` closes, so it is not a missing instance in general. Do not
chase it: **prove a dedicated lemma computing the hom on the specific difference
you need and mark it `@[simp]`** — here `stepanovEvalHom3_C_X_sub_X`, one line by
`simp [<the two defs>]`. This is the standing "printed pattern equals printed
target ⟹ use a defeq-checking tactic" rule with a new symptom: the forward
direction of a `map_*` lemma is what breaks, and the backward direction is fine.

### The scratch runner must use the TOOLCHAIN's `lean`, and must NOT `cd` out of the worktree

Two failure modes in one command, both of which read as a corrupt olean farm.
`lean` on `PATH` is elan's SHIM, and elan picks the toolchain from the CURRENT
DIRECTORY's `lean-toolchain`. So `cd /tmp/scratch && lean f.lean` selects whatever
elan's default is — here `v4.32.0` against the project's `v4.32.0-rc1` — and dies
with

    failed to read file '…/leanprover--lean4---v4.32.0/lib/lean/Init.olean',
    incompatible header

which looks like a damaged `LEAN_PATH` farm and is a wrong-binary error. And the
Bash tool's working directory PERSISTS between calls, so one stray `cd` poisons
every later run. Wrap the loop in a two-line script that `cd`s to the worktree and
invokes the toolchain binary by absolute path:

    cd /home/chend/flt-lean-N
    env LEAN_PATH="$(cat lp.txt)" LEAN_SRC_PATH="$(cat lsp.txt)" \
      ~/.elan/toolchains/leanprover--lean4---v4.32.0-rc1/bin/lean "$1"

Measured on a 61 000-line module whose full build is ~40 minutes: **5.7 s** per
scratch round against the release oleans, and every one of the ten new declarations
in this task went green in the scratch and compiled unchanged in the real file.

