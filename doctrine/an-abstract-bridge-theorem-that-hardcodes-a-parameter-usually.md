## AN ABSTRACT BRIDGE THEOREM THAT HARDCODES A PARAMETER USUALLY HAS A FREE GENERALISATION INSIDE ITS OWN INTERFACE
(2026-08-02, `flt-lean-52`, on `translationDatum_of_tameBase` in
`FreyCurve/IsogenySignature.lean`.) This development is full of theorems of the shape
*"given an abstract base `(L, A, resEquiv, π)` together with a MEMBERSHIP CRITERION
`hmem`, and given some inequalities, build the datum"*. They are written for one consumer,
and they routinely hardcode a parameter to the value that consumer needed — here the
translation `r` was hardcoded to `0`, and had been since the theorem was written.
**Before concluding that the general parameter needs a bigger interface, ask which values
of it stay INSIDE the interface you already have.** `hmem` decides `π^m · x ∈ A` for
`x : ℚ` **only**. So:
* `r : L` is genuinely out of reach — the three conditions become memberships of elements
  of `L`, and deciding them needs the full valuation theory of the base;
* `r : ℚ` is FREE — every quantity in the conditions (`3r`, `a₄ + 3r²`, `f(r)`) is again
  RATIONAL, so `hmem` applies verbatim and the proof is the old one with three extra
  `A.zero_mem` branches for the degenerate case where the rational is `0`.
Nobody had noticed there was a case strictly between "the special value" and "the general
element". It cost ~100 lines and closed a real family of curves.
**MEASURE THE NARROWING WITH A WITNESS, and put the witness in the docstring.** A recut
that trades one leaf for one leaf is indistinguishable from a rename unless you can name a
consumer of the old leaf that the new one no longer owes. Here that is `y² = x³ + 8` at
`q = 3`: it satisfies every hypothesis of the old leaf, PARI's `elllocalred` confirms it is
genuinely additive there (conductor exponent `2`, Kodaira `III`, so it was not already
good), `r = 0` fails on it (`2·v₃(8) = 0 < 3 = v₃(Δ)`) and `r = 1` succeeds. Equally
important is the witness the narrowing does NOT reach — `y² = x³ + 4` at `q = 3`, where a
rational `r` would need `r³ ≡ 5 (mod 9)` and the cubes mod `9` are `{0, 1, 8}` — because
that is what shows the hard content stayed in the leaf rather than being quietly weakened.
Two riders.
* **Keep the OLD name as the PROVEN theorem and give the NEW leaf a new name.** The recut
  is then invisible to every consumer, and a queue entry naming the old name fails loudly
  (it points at a proven declaration) instead of silently dispatching someone at nothing.
  Say so in `to_merger`; a warning-set delta of `−1 +1` carries no information about which
  name moved.
* **`push_cast` does not push `algebraMap ℚ L 3`.** Numerals crossing a `RingHom` need
  `map_ofNat` named explicitly; without it `push_cast; ring` fails leaving a goal whose two
  sides differ only by `(algebraMap ℚ L) 3` versus `3`, which reads as a `ring` failure and
  is not one. Same for `simp` on a hypothesis `congrArg (algebraMap ℚ L) h`: use
  `simp only [map_add, map_mul, map_pow, map_ofNat, map_zero]`, never bare `simpa`, which
  will instead normalise the GOAL through `mul_eq_zero` and report a mismatch between two
  things it never tried to connect.
### The wall behind it, measured: there is exactly ONE residue-degree-`1` base in this project
Worth knowing before pricing any leaf that has to produce a number field with a prescribed
prime of residue degree `1`. The only such construction in the tree is `TameBaseAux`'s
`ℚ(q^{1/12})` (`EllipticCurve/TorsionReduction.lean`, lines 638–1422, **784 lines**), and
it is REFUTED at both wild primes by witnesses already recorded in `IsogenySignature.lean`.
The general construction is `ℚ[X]/(g)` for `g ∈ ℤ[X]` monic Eisenstein at `q` — unique
prime above `q`, totally ramified, residue degree `1`, and every totally ramified extension
of `ℚ_q` arises this way — and formalising it is a port of those 784 lines with `12`
replaced by `deg g`. The only step that is not a mechanical substitution is
`v(π)^{deg g} = v(q)`, a three-way case split closed by `Valuation.map_sum_lt` off
`q ∣ g.coeff i` and `q² ∤ g.coeff 0`; `exists_repr`, `padicValRat_coeff_nonneg` (whose
"pairwise distinct mod `12`" becomes "mod `n`"), `exists_tameResidueHom` and the DVR
instance all transfer verbatim. **Chevalley extension does the whole valuation-subring
half for an arbitrary finite extension of `ℚ` already** (`LocalSubring.exists_le_valuationSubring`),
so none of that is base-specific; what is base-specific is exactly residue degree `1`, and
that is what the `mod deg g` distinctness argument buys.
