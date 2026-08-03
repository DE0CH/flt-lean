## WHEN A PROVEN THEOREM'S PROOF DISCARDS A CONJUNCT OF ITS OWN INPUT, THE REFINEMENT THAT KEEPS IT IS CHEAP — AND IS USUALLY THE BRIDGE YOU ARE MISSING
(2026-08-01, `flt-lean-343`, recutting `exists_hauptmodul_of_weierstrassModel_gamma0Datum`
in `ModularCurve/X0.lean`.)
`exists_stableCyclic_of_gamma0Datum` — "a `Γ₀(N)`-datum over `Spec ℚ` IS an elliptic
curve with a Galois-stable cyclic subgroup" — is PROVEN, and its first line is
    obtain ⟨E, hE, -, he⟩ := exists_weierstrassModel_geomFibreAddEquiv_of_ellipticScheme ab hdim
The `-` is an `IsWeierstrassModel ab E` that the upstream theorem *does* hand over and
that this one throws away, deliberately and with a docstring explaining why (it wanted to
keep coordinate data out of that module). The consequence, which no docstring records: the
curve it returns is related to nothing — in particular **nothing can be said about its
`j`-invariant**, so the theorem is unusable for any consumer whose conclusion mentions `j`.
Keeping the conjunct costs one changed `obtain` pattern and one extra line
(`weierstrassModel_j_unique ab E' E hmodel' hd`), and it turns "some curve with a stable
subgroup exists" into "**a curve with the same `j` as yours**". That was the entire missing
bridge between a moduli-level leaf and its point-level content.
**The check is mechanical and worth running on any PROVEN theorem you are about to route
around: read its proof's `obtain`/`rcases` patterns for `-` and `_`.** A discarded
component of an upstream conclusion is a refinement nobody has stated, it is almost always
a handful of lines, and the reason it was discarded is usually a module-hygiene decision
rather than a mathematical one — so it does not bind you.
### And the arithmetic that follows: check whether your leaf is EQUIVALENT to its own consumer
Running that bridge here showed that the datum-level leaf and the point-level theorem two
declarations below it (`exists_x0GenusZeroHauptmodul`) are **interderivable** —
`exists_weierstrassModel_gamma0Datum` goes point → datum, the new bridge goes datum → point
— so the ~120-line coarse-moduli layer between them (`exists_x0GenusZeroJMapHauptmodul`,
which builds `Y_0(q)` and its `j`-map only to feed that one consumer) is a **round trip**.
That is a real finding and it is also a trap, because the obvious repairs are both wrong:
* **restating the leaf at the point level DUPLICATES the consumer** — one sorried copy
  upstream, one proven-through-a-detour copy downstream, which is exactly the
  rival-cut cycle this file spends pages on;
* **deleting the detour** orphans proven work in the most-edited file in the repository.
CLAUDE.md's own tie-break decides it: when two arrangements are equivalent (neither root is
strictly implied by the other), **"already integrated and consumed by neighbours" wins — do
not restructure.** So the leaf stays at the datum level and the detour stays.
**What is still available, and is what to do: recut so the residual sheds VOCABULARY without
duplicating an existing statement.** Here the bridge hands back `E'` and not `E`, so the
residual has to be stated about a rational number with the curve bound existentially
(`exists_hauptmodul_of_exists_stableCyclic`) — and that j-abstraction is simultaneously what
makes it *not* a copy of `exists_x0GenusZeroHauptmodul` and what the assembly genuinely
needs. Count `1 → 1`; what left the leaf is `Gamma0Datum`, `AbelianSchemeStruct`, `SpecQ`
and `IsWeierstrassModel`. **The receipt for a recut is one line and belongs in the commit:**
    git diff <file> | grep -cE '^\+ *sorry *$'   # 1
    git diff <file> | grep -cE '^- *sorry *$'    # 1
### A scratch that imports `X0.lean` needs its two SCOPED opens, or a real declaration reads as missing
`X0.lean:1085–1086` are `open CategoryTheory AlgebraicGeometry` and
`open scoped WeierstrassCurve.Affine`, and a scratch that omits the second gets
    Invalid field `Point`: The environment does not contain `WeierstrassCurve.Point`
on `(E⁄(AlgebraicClosure ℚ)).Point`. The `⁄` notation is declared FOUR times in mathlib
(`Weierstrass.lean`, `Affine`, `Jacobian/Basic.lean`, `Projective/Basic.lean`), all
`scoped`, and without the `Affine` one it resolves to the plain `WeierstrassCurve`
base-change, whose `.Point` does not exist. The message names a missing *declaration*, so it
reads as a stale olean or a renamed lemma; it is a missing `open`. Omitting the first open
instead makes `≫` and `𝟙` fail as `expected token`, which at least points at notation.
**Copy the target file's top-level `open` lines verbatim into the scratch — all of them,
including the `scoped` ones — before debugging anything else.**
**AND THE REVERSE, WHICH IS THE ONE THAT COSTS A ROUND: a scratch whose opens are MORE
generous than the paste site's compiles text the file will reject.** Fixing the `⁄` error
above by adding `open _root_.WeierstrassCurve` let the scratch accept the short spelling
`Affine.Point.map`; `X0.lean` does open that, at 28343 and 29816, but both openings have
been closed again by line 30486, so the same three lines came back as
`Unknown identifier Affine.Point.map` on the real elaboration — 8 minutes, after a 10-second
scratch had said green. This is the standing "a scratch cannot check DECLARATION ORDER" rule
with SCOPE substituted for order, and it has the same cure: **before pasting, read the
paste site's neighbours and copy their spelling of every name.** `exists_weierstrassModel_`
`gamma0Datum_liesIn`, 220 lines above, writes `WeierstrassCurve.Affine.Point.map` in full —
which is the file telling you the short form is not in scope there.
