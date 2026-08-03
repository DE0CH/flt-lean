## TWO DIOPHANTINE BRANCHES CAN BE ONE CURVE — LOOK FOR A RATIONAL INFLECTION POINT
(2026-07-31, `flt-lean-15`, `mul_eq_zero_of_thirtySevenB_oddCubic` in
`FreyCurve/MazurTorsion.lean`.)  A descent leaf in this tree routinely folds several
cube/square classes into one statement with a disjunction — here `(e, f) = (1, 296)`
or `(37, 8)`, "two equations serve three classes".  Before accepting the disjunction
as irreducible, ask whether the two equations are the SAME plane curve in disguise.
They very often are, because every class that SURVIVES the local sieve is by
construction in the image of the descent map, hence its homogeneous space has a
rational point, hence all the survivors are isomorphic to the same Jacobian.
**The mechanical test is one line per branch: is the leaf's own trivial solution an
INFLECTION point?**  Compute the tangent at it, substitute the tangent back into the
ternary form, and see whether the residue is a perfect cube in the remaining
variable.  Here `[1 : 1 : 0]` gave residue `−s³` and `[−2 : 0 : 1]` gave `−n³/27`, so
both are inflections.  **A plane cubic with a rational inflection point is LINEARLY
equivalent over the base field to a Weierstrass model** (put the inflection at
`[0 : 1 : 0]` and its tangent at infinity), so two such cubics with the same Jacobian
are related by an explicit element of `PGL₃(ℚ)`.  Reduce each to Weierstrass form,
match, and eliminate: here that produced
    (m, n, r) ↦ (4r, −2m, −n),   with   F₁(4r, −2m, −n) = 8·F₂(m, n, r)
exactly — so the second branch is proved from the first by `linear_combination 8 * h`
plus a case split on the one coordinate the map sends to the third slot.  Six lines,
`ring`-checked, and the leaf goes from two cubics to one.
Three riders, each of which cost real time here:
* **`ellfromeqn` gives the CUBIC'S OWN Jacobian, and that is NOT the curve the
  descent started from.**  The covering `C_d → E` is degree `3` (recovering the
  coordinates needs a cube root), so `C_d` is a torsor under the ISOGENOUS curve.
  This leaf's docstring said "it is the Mordell–Weil rank of `37b1`" — true as a
  consequence, and misleading as a description: the cubics' Jacobian is `37.b3`,
  which unlike `37.b1` has **TRIVIAL** torsion.  That is the sharper statement to
  check a proof against (`C(ℚ)` is a SINGLE point), and it is invisible until you
  run `ellfromeqn` on the cubic rather than `ellinit` on the curve you came from.
* **The two stages of an isogeny descent land in DIFFERENT cohomology groups, and a
  docstring that just says "the second descent is what is missing" will send a prover
  hunting for a family that does not exist.**  If `ker φ ≅ ℤ/3` with trivial action
  (a rational `3`-torsion point), the Weil pairing forces `ker φ̂ ≅ μ₃`.  So the
  `φ̂`-descent lands in `H¹(ℚ, μ₃) = ℚ*/(ℚ*)³` — Kummer, the familiar "classes `d`" —
  while the `φ`-descent lands in `H¹(ℚ, ℤ/3) = Hom(G_ℚ, ℤ/3)`, i.e. twists indexed by
  CYCLIC CUBIC FIELDS.  Only the first is a cube-class computation.  Say which one a
  residual leaf needs.
* **For a completeness sweep of `f·r³ + c₁·r + c₀ = 0`, use the RATIONAL ROOT THEOREM
  (`r ∣ c₀`), never a Cauchy bound.**  The Cauchy bound for this family runs to `10⁷`
  and makes the honest "complete in `r`" sweep unaffordable — a previous audit's box
  was `|m|, |n| ≤ 300`; the divisor enumeration reached `400` in seconds.
**And record the norm form if you find one.**  An invertible linear change of
coordinates turned this cubic into `T·((T + 30W)² + 27U²) = −4W³`, i.e.
`T · N_{ℚ(√−3)}(λ) = −4W³` — the shape a `ℤ[ζ₃]` factorisation descent wants, and
`ℤ[ζ₃]` is a PID.  Deriving it is half a day and it is not visible from the cubic, so
it belongs in the docstring whether or not you can finish the descent.
