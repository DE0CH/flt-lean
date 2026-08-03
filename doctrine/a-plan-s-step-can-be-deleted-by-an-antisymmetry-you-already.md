## A PLAN'S STEP CAN BE DELETED BY AN ANTISYMMETRY YOU ALREADY HAVE — ask whether you need BOTH directions
(2026-08-01, `flt-lean-262`, closing `PlaceData.pt_surjective_of_isAlgClosed` in
`ModularCurve/HyperellipticJacobian.lean`.)  That leaf carried a six-step PROOF PLAN, worked
out the day before, every input of which existed and was proven.  The plan was correct.  Its
**step 2 was unnecessary**, and step 2 was the mechanical-but-bulky one: *"generalise
`exists_localDenom_affine` / `exists_localDenom_infinite` from `pt P` to an arbitrary place"*,
i.e. copy a ~50-line proof twice with its last line changed.
The uniqueness half is *"`v` and `pt P` have the same chart values ⟹ `v = pt P`"*, and the
plan proved it by showing the two valuation rings are EQUAL — which needs the local-ring
description at BOTH places, hence at an arbitrary one, hence step 2.  But **distinct
normalised valuation rings on one field are INCOMPARABLE**, so ONE inclusion already forces
equality, and the inclusion in the direction that the EXISTING lemma gives is the one you can
have for free.  Step 2 deleted; uniqueness became three lines per chart.
The incomparability is itself cheap and worth knowing as a standing tool (`~30` lines from
the bare axioms `ord_mul`, `ord_add`, `ord_inv`, `ord_surjective`): from `O_w ⊆ O_v` first
get `m_v ⊆ m_w` (if `ord w x ≤ 0` then `x⁻¹ ∈ O_w ⊆ O_v`, so `ord v x ≤ 0`), then for a
uniformiser `t` at `v` and `k := (ord w t).toNat`, the element `z ^ k * t` has positive order
at `v` — hence at `w` — while `k · ord w z + ord w t ≤ −k + ord w t = 0` whenever
`ord w z < 0`.
**The generalisable check, and it costs one question: when a plan proves `A = B` by proving
`A ⊆ B` and `B ⊆ A`, ask whether the ambient structure makes one inclusion imply the other.**
Antisymmetry-for-free is common and is exactly what a plan written in mathematical prose
elides, because on paper "and symmetrically" is one word.  In Lean it is half the work, and
here it was the half that needed new code.  Other instances of the same shape in this
development: two normalised discrete valuations, two maximal ideals, two valuation rings, two
places, two subgroups of the same finite index, two submodules of the same finrank.
* **Grep for your helper's name before declaring it, even a three-line one.**
  `aeval_xx_ne_zero` — "a nonzero polynomial does not vanish at the transcendental abscissa" —
  already existed, 6 400 lines above, proved a different way (`transcendental_iff_injective`
  rather than by unfolding `Transcendental`).  A duplicate of a three-line lemma is invisible
  to `dupstmt.py`'s default scope (it scans SORRIED declarations) and to `xdup.py` (which is
  about cross-FILE name collisions), so nothing would have caught it.  The check is one
  `grep -rn "^\(theorem\|lemma\) <name>" --include=*.lean Fermat/` per helper.
* **A plan that names its inputs is worth far more than one that names its conclusion, and
  this one earned its keep.**  Every one of the ~20 declarations it cited existed, was proven,
  and had the generality it claimed — including the observation that `exists_localDenom_chart`
  takes an ARBITRARY place, which is what made the whole thing tractable.  Verify that claim
  first (one `sed` on the signature); it is the cheapest possible test of whether a plan was
  written by someone who read the file.
