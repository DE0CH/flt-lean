## "THE EXPENSIVE STEP IS THAT IT HAS NO OTHER ZEROS" — CHECK WHETHER THE CONSUMER WANTS THE ZERO **LOCUS** OR ONLY **DIVISIBILITY**

(2026-08-01, `flt-lean-103`, `modularForm_levelOne_eq_zero_of_valence` in
`ModularCurve/X0.lean`.)  A leaf whose content is "the classical theorem `T`" often carries
a docstring that names a CHEAP first step and prices everything else as one lump.  This one
did it in a single sentence, and the sentence was the whole error:

> The cheap first step is the two vanishing FACTS — `E₄(ρ) = 0` … and `E₆(i) = 0` …; **the
> expensive step is that they have NO OTHER zeros, which is the valence formula proper.**

The consumer never needs the zero LOCUS.  What the induction consumes is
**`E₄ ∣ F` whenever `F(ρ) = 0`** — divisibility in the graded ring — and that is a strong
induction on the weight over machinery mathlib already has: subtract off a multiple of a form
with constant term `1` (an Eisenstein series, or `1` in weight `0`), divide the resulting CUSP
form by `Δ` (`CuspForm.discriminantEquiv`), and recurse at `k − 12`.  No dimension count, no
monomial basis for `ℂ[E₄, E₆]`, and no statement whatever about where `E₄` vanishes.  ~350
lines, and it closed the entire algebraic half of the node.

**The generalisable check, and it is one careful read of the consumer's proof: for a leaf about
a specific function `g`, list which of `g(x) = 0`, `ord_x g = 1`, `g⁻¹(0) = {orbit of x}` and
`g ∣ F` the argument actually uses.**  Those four are wildly different in cost — the first is an
automorphy computation, the last is an induction over an existing division theorem, and only the
middle two are analysis.  A docstring written by whoever CUT the leaf normally names the one the
CLASSICAL PROOF uses, which is routinely the zero locus, because that is how the textbook
narrates it.

**What was genuinely left is worth stating in the sharp form, because it is one line and it is
the ONLY analysis in the node:** `ord_ρ E₄ ≤ 1` and `ord_i E₆ ≤ 1`.  Both are SHARP in the
strong sense that the target theorem is FALSE without them — at `ord_ρ E₄ = e ≥ 2` take
`F = E₄`, `k = 4`, `b = e` — so this is not a weakening, it is the residue.

**And a `≤` leaf is the right shape when the `≥` half is free.**  `1 ≤ ord_ρ E₄` follows from
`E₄(ρ) = 0`, so state the leaf as `≤ 1`, not `= 1`: the assembly only ever adds it on the large
side (`ord F = ord E₄ + ord G ≤ 1 + ord G`), so a `≤` leaf is strictly weaker and loses nothing.

Two riders, both measured on this node:

* **An automorphy relation can NEVER supply the simplicity of an elliptic zero, and it is worth
  writing that down so nobody tries.**  Differentiating `E₄(γz) = (z+1)⁴E₄(z)` at the fixed
  point gives `e ≡ 1 (mod 3)` and then the first-derivative relation is exactly vacuous
  (`1/(ρ+1)² = (ρ+1)⁴` on the nose, both `= ρ²`).  Every algebraic consequence of the graded
  ring is likewise invariant under replacing `e` by any member of that congruence class — I
  checked the dimension-count and filtration arguments and `e` never enters.  So a leaf of the
  form "this zero is simple" is a genuine analytic input, and the cheapest one in the pin is the
  SERRE DERIVATIVE (`Derivative.serreDerivative`, whose slash-equivariance and `MDiff`-ness
  mathlib already has); its one missing input is `IsBoundedAtImInfty (Derivative.D f)`, and
  `Derivative.lean` lists "Serre derivative preserves modularity" as an explicit TODO.
* **Put the development in a NEW module, not in the giant file.**  651 lines landed in
  `ModularCurve/LevelOneValence.lean`, which `lake build`s in **5 seconds**; `X0.lean` gains one
  `public import` and one `exact`.  Iteration on the mathematics was ~3 s per round against a
  ~30-minute `X0` rebuild, and the merge surface is one new file plus two hunks.

Small trap met on the way, since it will recur for anything stated about `X0.lean`'s
`ellipticRho`: a new module cannot see that definition, so restate the point locally with the
same body and let the consumer's `exact` cross the two by `rfl`.  Say in the module docstring
that the duplicate exists and which copy a cleanup should keep — re-pointing `ellipticRho`'s
other consumers is an interface edit in a contended file and is not a passer-by's job.

