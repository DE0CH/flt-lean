## A "WHAT IS STILL AVAILABLE" ROUTE PARAGRAPH INHERITS THE PARENT'S HYPOTHESES IN PROSE AND NOT IN THE BINDER LIST — WRITING IT OUT IN LEAN IS WHAT FINDS THAT

(2026-07-31, `flt-lean-138`, `Modularity/TateModule.lean`.)  A mature leaf here usually
carries a paragraph headed *"WHAT IS STILL AVAILABLE, so that a successor does not
re-derive it"*, giving the half of the argument that does go through.  Those paragraphs
are the most valuable prose in the file and they are written by the agent that CUT the
leaf, from the parent's proof — **so they are stated in the parent's scope, where the
parent's hypotheses are all present, and the cut copies the paragraph while the binder
list is retyped by hand.**  A hypothesis the paragraph silently uses can therefore be
missing from the child, and nothing flags it: the prose is correct, the leaf compiles,
the route reads as checked.

`exists_isUnit_rawConstant` was cut out of `exists_tateWeilRawFamily_of_qAdicWeilSystem`
and carries `hqe : q ∈ I^e` but NOT `hqe2 : q ∉ I^(e+1)`, which the parent has.  Its
route paragraph writes out the geometric half — *"write `q^N 𝒪_D = I^{e·N}·J` with `J`
coprime to `I`"* — and that factorisation is the statement `v_I(q) = e`, i.e. exactly
`hqe2`.  With only `hqe` the child is FALSE, and the witness is small: `D = ℚ(i)`,
`q = 2`, `I = (1+i)`, `e = 1`, where `v_I(2) = 2`, so `A[I] = π·A[I²]` and
`w(πu', πv') = w(π²u', v') = w(0, v') = 1` — the pairing is IDENTICALLY trivial on the
values of Tate points, `hLinj` puts every `Φ` in `(q)^N`, the FOURTH clause of
`IsTraceDualFunctional` forces `C N t s ∈ span {jπ} ⊆ 𝔪`, and clause 9 asks for a unit.

**The check is mechanical and is not the binder diff this file already prescribes.**
Diffing the child's binders against the parent's gives a long list of hypotheses the
child legitimately does not need; what identifies the ONE that matters is reading the
route paragraph for a step that *names an object it does not construct* — here "with `J`
coprime to `I`" — and asking which hypothesis produces it.  Do that before writing any
Lean, and again while writing it: **the reason this one was found is that the paragraph
was formalised rather than read**, and the ideal-theoretic step is where the missing
hypothesis becomes an unprovable goal instead of a plausible sentence.

Two riders.

* **Formalising a route paragraph is worth doing even when the leaf stays open.**  The
  geometric half became `exists_tatePt_weil_ne_one` (PROVEN) over a new mathlib-shaped
  `exists_add_eq_one_mul_mem_span_pow` (PROVEN, axiom-clean), so the arithmetic owner
  inherits a theorem instead of a paragraph, and the frontier did not move.  Report that
  honestly: `+246/−0` lines, sorry set `15 → 15`, every warning line shifted by exactly
  the insertion — which is the receipt that the change is a pure addition.
* **The coprime split needs no valuation theory.**  `Ideal.dvd_iff_le` (to divide is to
  contain, in a Dedekind domain) turns `(c) ≤ I^e` into `(c) = I^e·K`; `c ∉ I^{e+1}` is
  `K ⊄ I`; `(cⁿ) = I^{e·n}·Kⁿ` and `Ideal.IsPrime.pow_le_iff` give `Kⁿ ⊄ I`; maximality
  plus `IsCoprime.pow_left` give `I^{e·n} ⊔ Kⁿ = ⊤`.  No `HeightOneSpectrum`, no
  `intValuation`, no `normalizedFactors`.  `exists_mem_torsion_act_uniformizer_eq` in the
  same file already used this shape and nobody had lifted it out.

