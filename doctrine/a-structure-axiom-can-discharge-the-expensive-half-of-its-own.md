## A STRUCTURE AXIOM CAN DISCHARGE THE EXPENSIVE HALF OF ITS OWN CONVERSE — ASK WHAT YOU NEED ONLY *UP TO*
(2026-07-31, `GeomPic.below_surjective` in `ModularCurve/HyperellipticJacobian.lean`.)
That leaf asks that `below : Places(F̄) → Places(F)` be ONTO, for the constant field
extension `F = ℚ(x,y) ⊆ F̄ = ℚ̄(x,y)`.  Its docstring priced it as the extension
theorem for valuations *specialised to a constant field extension*, and named the
price honestly: produce a valuation FUNCTION on `F̄` restricting to `ord_v` **on the
nose**, i.e. with ramification index `1`.  That is [Stichtenoth III.6.3(b)], it is a
real theorem, and it is exactly what the SIBLING leaf
`constFieldExt_exists_uniformizer` — still open — asks for.  Three passes read that
and moved on.
**It is not needed, because `ord_emb` is a FIELD of the structure.**  `GeomPic`
*asserts*, for every geometric place `w`, that `ord_w ∘ emb = ord_{below w}` with no
ramification index.  So it is enough to produce ANY place `w` whose restriction is a
POSITIVE MULTIPLE `e · ord_v`: the axiom reads that restriction back as
`ord_{below w}`, and the normalisation axiom `D.ord_surjective` at `below w` hands
you a `t` with `e · ord_v t = 1`, so `e = 1` and `below w = v` by `ord_injective`.
The unramifiedness is *free at the point of use*; what is left is pure existence.
**The general check, and it is one careful read of the structure:** when a leaf's
route asks you to prove something ON THE NOSE — an equality, a normalisation, an
index equal to `1`, a canonical choice — list the structure's axioms and ask which
of them already assert that property of *every* inhabitant.  If one does, you owe
only the statement **up to the ambiguity that axiom removes**, and that is routinely
a much cheaper existence statement.  The failure mode is specific: the route was
written by whoever CUT the leaf, from the argument that would build the object *from
scratch*, at a time when the object's axioms were not what they are now.
Here the residue was ordinary lying over, and it fell to machinery the file already
had: `PlaceClassify.exists_ordAt_eq` presents `ord_v` as `ordAt 𝔭` on
`A = integralClosure ℚ[t] F`; `ℚ̄[t]` is integral over `ℚ[t]` coefficientwise so
`A' = integralClosure ℚ̄[t] F̄` is integral over `A`;
`Ideal.exists_ideal_over_prime_of_isIntegral` gives a prime over `𝔭`; and mathlib's
`exists_primeCompl_mul_eq_of_integer` (`O_{ordAt 𝔭} = A_𝔭`) is what shows the new
place's restriction is `≥ 0` wherever `ord_v` is.  The two charts `t = x`, `t = 1/x`
are the only reason it has two cases, exactly as in `finite_isPlaceFun_core`.
Three riders worth keeping:
* **Say explicitly which sibling this does NOT close.**  `constFieldExt_exists_uniformizer`
  is still owed, because it is what BUILDS `below` and `ord_emb` for a `ConstFieldExt`,
  which carries no `ord_emb`.  A reader who sees "unramifiedness was free" and deletes
  that leaf has broken the producer.  There is no circularity: the axiom is discharged
  once, by `exists_geomPic`, and consumers of a *given* `gp` may spend it freely.
* **`omega` treats `a * b` and `b * a` as DIFFERENT ATOMS.**  A proof of the
  `w z = e * o z` shape that ends in `omega` will fail with a counterexample naming
  both products when the hypothesis happens to be normalised the other way round.
  `rw [mul_comm]` first; do not go looking for a wrong coefficient.
* **`set c := …` leaves a local definition that `simp` zeta-unfolds**, which breaks
  the `⟨_, monic_X_pow_sub_C _ two_ne_zero, by simpa … using hroot⟩` idiom the tower
  boilerplate in this file uses.  Introduce the constant opaquely with
  `obtain ⟨c, hc⟩ : ∃ c, … = c := ⟨_, rfl⟩` instead.
### The same theorem was cut TWICE in one file, and the two cuts share no identifier
`geomPic_below_surjective` — top level, in the "four sub-leaves of
`geomPic_bc_injective`" block — is character-for-character `GeomPic.below_surjective`,
cut a day apart for two different consumers.  Every `sorry`-scan counted one theorem
twice; `own.py` and `leafstat.py` correctly reported both as unowned open work; and
nothing links them, because the only text they share IS the statement.  This is the
`[[flt-two-leaves-may-be-one]]` shape with the discovery step made concrete: **when
you close a leaf, grep the file for its own STATEMENT — the conclusion, spelled out —
not for its name.**  Here `Function.Surjective gp.below` finds both in one command.
And check the survivor for consumers while you are there.  A comment-stripped scan
found FOUR further open leaves in that module with no code use anywhere in `Fermat/`
(`GeomPic.exists_emb_of_divisor_invariant` — Hilbert 90, hard —, `geomPic_hilbert90`,
`geomPic_exists_bcDiv_of_divAct_fixed`, `geomPic_exists_finiteLevel_divisor`), all
leftovers of superseded cuts whose parents are proven by other routes.  That is the
seventh invisibility class, and a file that has been re-cut twice is exactly where to
expect it.
