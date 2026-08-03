## A CUT THAT RAISES THE SORRY COUNT IS RIGHT WHEN IT SURFACES A MISSING THEORY
(Same task.) `exists_splitHilbertBlumenthalRatModel_of_standardLevelModule` was
"Rapoport §1" — a book chapter — and its conclusion also carried a Galois 1-cocycle
`c` on `X₁ ⊗ ℚ̄`, `IsQGaloisCocycle`, an open-normal-kernel clause, and the moduli
data on EVERY twist by `c`. Splitting it `1 → 2` along GEOMETRY vs DESCENT takes the
module's direct-sorry count from 20 to **21**, and is still the right cut:
* the assembly discharges three clauses outright — `c := 𝟙` with
  `isQGaloisCocycle_one` and `N := ⊤` — so the geometry half never sees a cocycle,
  a twist, or an algebraic closure;
* and the descent half's step 1 is **fpqc descent for MORPHISMS of schemes**, which
  is nowhere in this tree (`GaloisDescent.lean` is a zero-declaration stub; this
  file's interface descends morphism PROPERTIES only). That obligation was
  previously buried inside a leaf advertised as "all of the geometry", where nobody
  would ever have costed it.
**Naming a missing theory is worth more than a count.** The generalisable test for
whether a `1 → 2` is disclosure rather than inflation: after the cut, can each half
be dispatched to someone who does not need the other's literature? Here one half
needs Rapoport and the other needs descent theory, and neither needs both.
Two things to get right when you do it:
* **the faithfulness audit is NOT inherited, and in this direction it is a
  STRENGTHENING.** The parent quantified `∃ c`; fixing `c = 𝟙` narrows it. The fresh
  audit here is one sentence — the moduli problem is `ℚ`-rational, so its solution
  exists over `ℚ` and needs no twisting, and the `∃ c` was vestigial from the
  pre-cut form in which the model had to be moved to a PRESCRIBED `ρ₀`. Write the
  audit and write what would change your mind;
* **check the ORDER of the descent half's route, and say it.** Transporting the
  family up to `ℚ̄` along the twist and back hits the `Fermat.PolarizationStruct`
  base-change obstruction, which is real and has a Weil-restriction counterexample
  (the ρbar-side twin escapes it only by carrying no polarization). Descending the
  isomorphism to `ℚ` FIRST and transporting along an isomorphism of `ℚ`-schemes
  does not. A route note that gets this backwards sends the next owner into a known
  wall.
