## THE CM SURVEY, DONE ONCE SO IT IS NOT REDONE: what this pin does and does not have

(2026-07-31, flt-lean-159, while working the `MazurCMForm` cluster in
`MazurTorsion.lean`.  Every line below was checked by `grep`/`ls` against
`.lake/packages/mathlib` at our pin, not recalled.)

Four leaves in this tree ask for complex multiplication in one form or another
(`minpoly_eq_of_isCMJInvariant`, `exists_isCMJInvariant_ne_of_not_equivalent`,
`nonempty_isCMByRamifiedMaximalOrder_geomPoint_mazurLevel`,
`Fermat.exists_cmEndomorphism_of_mem_isolatedCMJInvariants`).  Every one of them
is a *theory build*, and here is exactly which theory is missing, so the next
agent does not spend its first hour rediscovering it:

* **No lattices in `ℂ`, no analytic `j`-function, no uniformisation.**
  `Mathlib/NumberTheory/ModularForms/` has Eisenstein series, `Δ`, the `η`
  function and `q`-expansions — and no `j`, and nothing relating a lattice to an
  elliptic curve.  So Cox's route 3(a) is not "cite mathlib", it is "build the
  theory".
* **No class group of a NON-MAXIMAL order.**  `ClassGroup` in mathlib is for
  Dedekind domains; `ℤ[√−n]` of conductor `> 1` is not one.  The form class group
  and the Cox Theorem 7.7 isomorphism do not exist either.
* **No Hilbert/ring class polynomial, no ring class field.**
* The ALGEBRAIC route (Silverman *ATAEC* II, `E ↦ E/E[𝔞]`) is gated inside this
  tree rather than by mathlib: it needs `Ideal (End W)`, hence a `CommRing`
  instance on `End W`, and `WeierstrassCurve.End.mul_comm_charZero` is an OPEN
  LEAF; it also needs quotients by finite subgroups, which this tree lacks.

**And one trap that looks like it should be free and is not.**  Galois-STABILITY
of "`x` is a CM `j`-invariant" — `IsCMJInvariant n x → IsCMJInvariant n (σ x)` —
would narrow two of those leaves considerably (with it, "there are two distinct
CM `j`-invariants" collapses to "one of them is irrational").  It is NOT
available: **mathlib's `WeierstrassCurve.Affine.Point.map` maps between BASE
CHANGES of one curve `W'` over a fixed base ring, along an `F →ₐ[S] K`.**  It
does not transport a curve over `ℚ̄` along a ring automorphism of `ℚ̄` to the
different curve `W.map σ`.  That transport, and with it the transport of
`IsIsogeny` (whose `IsRationalMap` certificate is a polynomial identity in
`veluPointX`/`veluPointY`, so it does conjugate — the mathematics is easy, the
API is absent), is a real ~200-line build in `Isogeny.lean`.  Price it before
promising it.

> **CORRECTED 2026-08-01 (`flt-lean-179`): THE TRANSPORT WAS BUILT, and this
> paragraph's absence claim has been false since it was written into a tree that
> already contained the answer.**  Everything above about MATHLIB is still exactly
> right — `Affine.Point.map` really is base-change-only — and that is precisely
> what made the paragraph convincing.  But `Fermat/FLT/EllipticCurve/Isogeny.lean`
> has a `GaloisTransport` section carrying `Affine.Point.mapRingHom`,
> `Affine.Point.mapRingEquiv`, `conjHom`, `IsRationalMap.transport`,
> `IsIsogeny.transport`, `isRationalMap_conjHom_iff`, `isIsogeny_conjHom_iff`,
> `AddEquiv.conjAddMonoidEnd` and — the payoff —
> `WeierstrassCurve.End.mapRingEquiv : End W ≃+* End (W.map σ)`, all PROVEN.  Over
> it, `MazurTorsion.lean`'s `isCMJInvariantOfRel_algEquiv` is **~25 lines**
> (`map_j` for the `j`-invariant; `map_intCast` for the CM relation;
> `RingHom.map_closure` plus surjectivity for `Subring.closure {φ} = ⊤`).  The
> "~200 lines, price it before promising it" estimate was honest and is spent.
> See the section at the end of this file for how the machinery was eventually
> found — a listing of the module's SECTION NAMES, not a name grep — and for why
> a name grep cannot find it.

**What IS free, and was harvested 2026-07-31**: over `ℚ̄/ℚ`, `∃ σ, σ x = y` and
`minpoly ℚ x = minpoly ℚ y` are interchangeable in one line —
`Normal.minpoly_eq_iff_mem_orbit` (`Mathlib/FieldTheory/Normal/Basic.lean`).
Any CM leaf phrased with a `Gal(ℚ̄/ℚ)`-orbit should be restated with minimal
polynomials, where the arithmetic is visible and the bookkeeping is gone.

