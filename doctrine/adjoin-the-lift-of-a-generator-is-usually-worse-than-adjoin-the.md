## "ADJOIN THE LIFT OF A GENERATOR" IS USUALLY WORSE THAN "ADJOIN THE LIFT OF EVERYTHING"

(2026-07-31, `flt-lean-73`, closing step 1 of `exists_traceSubringDescent` in
`Patching.lean`.)  The classical recipe for a coefficient ring inside a complete
local ring with finite residue field is Teichmüller's: `kˣ` is cyclic, lift a
GENERATOR `ḡ` along `X ^ (#k − 1) − 1`, adjoin the lift.  The leaf's docstring
prescribed exactly that, and it is correct mathematics.  It is also the expensive
formalisation, for a reason that has nothing to do with the mathematics:
recovering an arbitrary `y ≠ 0` as `ḡ ^ m` needs
`Submonoid.powers` / `Subgroup.zpowers` / `mem_powers_iff_mem_zpowers`
bookkeeping, and that membership **timed out at `whnf` (200 000 heartbeats)
inside the file's ambient context while elaborating instantly in a two-line
isolated `example`.**  Restructuring — dropping the `set`s, splitting the Hensel
step into its own lemma — did not help; the timeout is a property of the
surrounding context, not of the tactic block.

The escape is to notice that **the generator was only ever there to make the
adjoined set a SINGLETON, and nothing needs it to be one**: `k` is finite, so
`Set.range τ` for the lift map `τ : k → R₀` is finite, and
`Algebra.finite_adjoin_of_finite_of_isIntegral` is stated for exactly a finite
set of integral elements.  Adjoining the Teichmüller lift of EVERY element makes
residual surjectivity a projection (`⟨τ y, subset_adjoin ⟨y, rfl⟩⟩`), deletes the
cyclic-group theory entirely, and the whole thing is ~20 lines.  Use `X ^ #k − X`
rather than `X ^ (#k − 1) − 1`: its derivative is `#k · X ^ (#k−1) − 1`, which
maps to `−1` on the nose since `(#k : k) = 0` (`FiniteField.cast_card_eq_zero`),
so the simple-root hypothesis needs no case split on whether the point is zero.

Generalises past this leaf: **when a recipe adjoins the lift/preimage of a
GENERATOR, ask whether adjoining the whole finite fibre is equally finite.**  If
it is, the group theory was never load-bearing — it was an optimisation of the
*ring*, and you are optimising the *proof*.  Same family as
[[flt-leaf-cost-estimates-are-hypotheses]]: a docstring route is a hypothesis
about cost, written before anyone tried.

Two mechanical traps from the same proof, each one round trip:

* **The monic witness for `IsIntegral R x` lives in `R[X]`, and passing an
  `A[X]` one is reported as a UNIVERSE error.**  `Polynomial.monic_X_pow_sub h`
  with `h : (X : A[X]).degree < n` fed to `⟨X ^ n - X, ·, ·⟩ : IsIntegral R x`
  gives `degree.{uR} X < ↑n` against `degree.{0} X < ↑n` — which reads as a
  `Type*` / universe-polymorphism problem and is not one.  The two `X ^ n − X`
  are simply polynomials over different rings.  Check the RING before touching
  the universes.
* `IsAdicComplete.henselianRing R I` gives `HenselianRing R I`, **not**
  `HenselianLocalRing R`, and mathlib has no instance from the first to the
  second.  Use `HenselianRing.is_henselian` directly: its simple-root hypothesis
  is `IsUnit (Ideal.Quotient.mk I …)`, which for `I = maximalIdeal R` you get
  from `IsUnit …` in `R` by `.map _`, and `IsUnit …` in `R` from
  `IsLocalRing.notMem_maximalIdeal` plus `IsLocalRing.ker_eq_maximalIdeal`.

### When your target module is downstream of a RED module, fill only the MISSING oleans from the release

Same run, and it is the sharp form of the shim recorded above.  `X0.lean` was red
on `merger` (≥100 errors, `maxErrors` reached — release-27 merge damage: dropped
arities on `etale_nTorsion_of_specQBase` / `isFinite_flat_nTorsion`, and
`exists_jSection` used above its declaration), and `X0 → MazurTorsion → Patching`
means `lake build Fermat.FLT.Modularity.Patching` could not reach the module at
all.  `lake` had already brought 5579 of 5597 targets up to date before dying, so
the right farm is **current `.lake/build` plus the release copy of exactly what is
missing** — not the release tree wholesale:

    python3 - # list modules under Fermat/ with no .olean in .lake/build/lib/lean
    cp -rs /scratch/chend-flt/flt-lean-N/.lake/build/lib /tmp/relean-N/      # symlinks, instant
    cp -f ~/.flt-release-lake/build/lib/lean/<the missing module>.olean* /tmp/relean-N/lib/lean/<dir>/
    LP=$(lake env printenv LEAN_PATH); LSP=$(lake env printenv LEAN_SRC_PATH)
    LEAN_PATH="/tmp/relean-N/lib/lean:$LP" LEAN_SRC_PATH="$LSP" lean <your file>

Here that was ONE module.  The soundness condition is the usual one — your file
must not name anything added to the substituted module since the release sha —
and it is much more likely to hold when you substitute one olean than when you
substitute the whole tree.  Say in the commit which oleans were substituted; a
shim-verified edit is not a build and must not be reported as one.

**AND WHEN THE SHIM ITSELF COMES BACK RED, DIFF IT AGAINST THE UNEDITED FILE —
that turns an unusable log into a clean verdict.**  The run above produced 52
errors, so on its own it says nothing about whether the edit is sound.  Running
the SAME shim on `git show <base>:<path> > /tmp/Pre.lean` gave 52 errors too, and
comparing the `(line, column)` pairs showed a single distinct offset —
`(+151, same column)` — which is exactly the number of lines the edit inserted
above them.  Identical error set, identical `declaration uses 'sorry'` set (8 in
both, at the same shifted lines).  That is a complete answer to "did I break
anything", and it costs one extra elaboration of a file you were going to
elaborate anyway.  It also detects the reverse — an error that DISAPPEARS is as
much a signal as one that appears, since it usually means a declaration stopped
being reached.

Do the comparison on `(line, column)` pairs and require the shift to be a single
constant; a mixed shift set means your edit changed more than it inserted.
