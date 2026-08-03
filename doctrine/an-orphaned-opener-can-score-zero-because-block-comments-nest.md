## AN ORPHANED OPENER CAN SCORE ZERO — because block comments NEST, and "unknown identifier" is its real symptom

(2026-07-31, `flt-lean-105`, `ModularCurve/RelativePicard.lean`.) The section above
says `depth > 0` names the culprit. That is true and it is not the whole story: **two
defects of opposite sign cancel, and then the balance scan reports the file as clean.**

`RelativePicard.lean` had an orphaned `/--` at ~4230 — the 2026-07-30 docstring of
`𝒪(−σ) COMMUTES WITH BASE CHANGE`, left truncated mid-sentence when a branch replaced
it — and a stray `-/` about 700 lines later, left by the *mirror* damage in a different
docstring. The file scored `depth = 0`. It did not report `unterminated comment` either,
because **Lean's block comments NEST**: the orphan simply swallowed everything up to the
first unmatched `-/`, and the nested `/-!`/`/--` in between raised and lowered the depth
on the way.

**So the symptom is not a comment diagnostic at all. It is:**

    error: Unknown identifier `relSection_comp_curveBaseChangeMap`
    error: Unknown identifier `isPullback_curveBaseChangeMap`
    error: Unknown identifier `exists_abelJacobiPoint`
    error: Unknown identifier `exists_relPicZeroGroupScheme`

for four declarations that `grep -c '^theorem <name>'` finds **exactly once each**. That
combination — *the compiler says a name does not exist, and the source says it does* —
has exactly two causes in this tree, and they are told apart in one command:

* the declaration is BELOW its use (Lean's linear order), which
  `grep -n` settles instantly; or
* **the declaration is inside a comment nobody can see.** Look UP from the first
  reported name for the nearest `/--` or `/-!` and check that it closes before the
  declaration; a docstring that ends mid-sentence is the tell.

Both were present here, which is why fixing the first alone changed nothing.

**Consequences for the release checks.** The nesting-cancellation case is invisible to
`flt-comment-balance.py` by construction, so the balance scan is a cheap FIRST pass and
never a clearance. It stays worth running — it found four files in one release — but
the only instrument that sees this one is `lake env lean` on the single file, which is
minutes rather than a full build. Run it on any module whose errors are a list of
"unknown identifier" for names that exist.

And it argues for one habit when REPAIRING this class: after deleting an orphaned
opener, re-run `lake env lean` even if the scan now reports the file balanced — the
deletion *unmasks* whatever the stray `-/` was hiding, and here that was three further
defects (a second orphaned header, a pair of `_`-prefixed binders used unprefixed in a
body, and a genuine declaration-order break). Repairs in this class arrive in layers,
for the same import-graph reason the release build takes three rounds.

### THE DETECTOR: `tools/merge/commentspan.py`, and the signal is NOT span length

(2026-07-31, `flt-lean-118`. The section above says the only instrument that sees a
cancelling swallow is `lake env lean` on the single file. That was true and it is a
bad deal, because the modules where this happens are exactly the ones that cannot be
built — `Patching.lean` and `Interface.lean` are both downstream of `X0.lean`, which
has been red since release 25.) There IS a static detector, it needs no oleans, and it
runs over the whole tree in two seconds:

    python3 tools/merge/commentspan.py           # 3 reports on this tree, all real

**A legitimate docstring never contains a line that begins a TOP-LEVEL DECLARATION at
column 0.** A block comment that does is a swallow. That is the discriminator, and
getting it wrong in either direction is easy:

* **span length alone is useless** — this project writes 400–800 line module essays,
  so thresholding at 400 lines gives 21 reports of which most are honest;
* **"contains one declaration" alone is useless too** — the docstrings here quote
  Lean at column 0 constantly (route sketches, rejected statements), which gives
  **577** reports. Requiring **five** declarations gives three, and all three are
  wounds. `--min-decls 3` (15 reports) is the eyeball-review setting.

What it found the day it was written, none of it visible to `flt-comment-balance.py`,
`scopecheck.py`, or any build:

    Interface.lean:39911 -> :81532   41621 lines,  644 declarations swallowed
    X0.lean:80904        -> :82118    1214 lines,   47 declarations swallowed
    X0.lean:37098        -> :38245    1147 lines,   17 declarations swallowed
    Patching.lean:10134  -> :12114    1980 lines,  ~30 declarations swallowed  (repaired)

**The shape is always the same and so is the repair**: two branches wrote rival
docstrings for one theorem, the merge kept BOTH `/--` openers and ONE `-/`. Delete the
STALE opener (the live docstring is a few dozen lines below it, and its own header
usually says PROVEN where the stale one says SORRY LEAF), then find the mirror half —
the `-/` that has just become stray — and reopen the bare prose above it as `/--`.
`X0.lean:82118` is on release 27's own list of remaining parse errors, which is the
same wound seen from the other end.

### WHEN THE MODULE CANNOT BE BUILT, RUN THE FILE BOTH WAYS AND DIFF THE ERRORS

Same task, and it is the general technique for editing a module whose cone is red.
`lean <file>` against a FIXED (possibly stale) olean set is not trustworthy in
absolute terms — the doctrine's inconsistent-olean warning applies in full — but it is
perfectly trustworthy as a CONTROL. Run the pre-edit file (`git show <sha>:<path> >
/tmp/Before.lean`) and the post-edit file against the same oleans, and every error
that survives with its line number shifted by exactly your edit's delta is not yours.

Measured here on `Patching.lean`: 52 error lines before, 18 after, every survivor at
+1085 = (1111 deleted − 26 added), and the 34 that vanished were precisely the wound's
signature — `invalid use of explicit universe parameters, IsCohenCoefficients is a
local variable` (a swallowed `def` had become an auto-bound implicit), two
`Unknown identifier`s, and four `Function expected at`. That is a complete, auditable
verification of a 1111-line deletion in a module that cannot be compiled at all, and
it cost two `lean` runs.

