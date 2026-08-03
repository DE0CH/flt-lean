## A LEAF PRICED AT A COUNTING THEOREM (`Σ e f ≤ n`) USUALLY NEEDS ONLY ONE OF THE TWO FACTORS — AND NORMALISATION ALREADY PINS `e`
(2026-08-02, `flt-lean-86`, closing `pt_infinite_of_ord_xx_neg` in
`ModularCurve/HyperellipticJacobian.lean`.)  That leaf — *the only poles of the abscissa are
the two points at infinity* — carried a confident and entirely correct route note pricing it
at the **fundamental inequality** `Σ_{v | ∞} e(v)·f(v) ≤ [F : K(x)] = 2` (Stichtenoth
III.1.11), and adding that it *"should be DELETED rather than proven separately"* once the
Riemann–Roch leaf `degOf_poleDivisor_eq_finrank_of_transcendental` lands.  Neither the
inequality nor the Riemann–Roch layer is used in the proof, and the deletion advice is wrong.
**A `Σ e f ≤ n` bound is TWO independent facts, and a leaf almost never needs both.**  Split
it before pricing anything:
* the **RAMIFICATION** half (`e = 1`, i.e. the pole is simple) is a statement about ONE place
  and is usually available from normalisation alone.  In this development `PlaceData` has
  `ord_surjective` as an AXIOM — the value group is exactly `ℤ` — so `e = 1` is EQUIVALENT to
  *"every element's order is a multiple of `e`"*, which is an elementwise divisibility
  statement and needs no degree theory at all;
* the **INERTIA / counting** half (there is no SECOND place on the same branch) is a
  UNIQUENESS statement, and uniqueness of a place is usually already proven somewhere in a
  file that has local rings — see the next section.
**The value-group computation, which is the reusable half and needs no Hensel and no power
series.**  For a degree-`2` extension `F = K(u)(w)` with `w² = h(u)` and a place with
`ord u = n > 0`, `ord w = 0`: take `g = P(u) + Q(u)w` and its CONJUGATE `ḡ = P(u) − Q(u)w`.
Then
    g·ḡ = (P² − Q²h)(u)     g + ḡ = 2·P(u)     g − ḡ = 2·Q(u)·w
are all in the base up to a unit, so all three have order in `nℤ`.  Recurse on `X ∣ P ∧ X ∣ Q`
so that one of `P`, `Q` has nonzero constant term, hence is a UNIT at the place.  Then:
* `ḡ = 0` ⟹ `g = 2P(u)` and `ord g = ord P(u) = ord Q(u) = 0`;
* `ord g ≠ ord ḡ` ⟹ the smaller is `ord(2P(u)) ∈ nℤ`, and the larger is `ord(gḡ)` minus it;
* `ord g = ord ḡ` ⟹ `ord g ≤ ord(g+ḡ) = ord P(u)` and `ord g ≤ ord(g−ḡ) = ord Q(u)`, one of
  which is `0`; and `ord g ≥ min(ord P(u), ord(Q(u)w)) ≥ 0`.  So `ord g = 0`.
**The degenerate case handles itself**, which is what makes this cheap: `h` being a square in
`K(u)` is exactly `ḡ = 0` for some `(P, Q)`, and that branch gives `ord g = 0` outright — so no
separate "the sextic is not a square" argument is needed, and neither is a square root of `h`
in `K[[u]]` (the file's `exists_powerSeries_sqrt` was NOT used).  Total: ~200 lines.
**Then `ord_surjective` finishes it**: pick `t` with `ord t = 1`, and `n ∣ 1`.
