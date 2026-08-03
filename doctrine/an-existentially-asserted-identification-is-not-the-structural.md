## AN EXISTENTIALLY-ASSERTED IDENTIFICATION IS NOT THE STRUCTURAL ONE — the `α`-gap
(2026-07-31, found decomposing `nonempty_isNIsogenyPair_of_gamma0Model`.) A "pin" definition of the
shape
    IsModelOf X d := <structural clause tying d to X> ∧ ∃ e : <points of X> ≃ <points of d>, <e is nice>
has a hole that no reading of either clause alone reveals: **nothing says the asserted `e` is the
identification the structural clause induces.** Write `ε` for the structural one. Both are "nice"
equivalences, so they differ by `α := ε⁻¹ ∘ e`, an automorphism satisfying every stated niceness
condition — and every downstream clause stated about `e` is then about a *different* object from
the one any construction out of the structural clause produces.
Concretely here: `IsGamma0ModelOf`'s model clause (added 2026-07-28 to fix the previous version of
this same hole) gives a Weierstrass chart `Spec ℚ[E] ↪ d.E`, hence `ε`; the level clause pins
`d.cyc` to `e(⟨g⟩)`; and the isogeny one can actually build from the chart has kernel `ε(⟨g⟩)`.
They agree iff `α(⟨g⟩) = ⟨g⟩`, which over `ℚ` is TRUE but only by **Tate/Faltings**
(`End_{Γ_ℚ}(T_ℓE) = End(E)⊗ℤ_ℓ = ℤ_ℓ`, so `α` is a `ℤ̂ˣ`-scalar on torsion). So the 2026-07-28
repair did not remove the Faltings-strength input the pin's own docstring says is absent — it
**moved** it, from "produce a morphism" to "identify the two identifications". That is the
characteristic failure mode: the hole reappears one level down, wearing the previous fix as
evidence that it was closed.
Two rules follow.
- **When a definition carries both a structural clause and an existential identification, check
  whether anything relates them.** If not, that gap is a leaf, and it is invisible to every
  faithfulness audit that reads the clauses one at a time — each is individually true and
  individually load-bearing (this is the same shape as the "two individually-correct repairs" entry
  above, at definition granularity rather than across two edits).
- **Isolate it as its own named leaf rather than burying it in the hard one.** Here it is
  `Fermat.liesIn_congr_of_geomFibreAddEquiv`, whose docstring records both how to prove it
  (Faltings) and how to make it *unnecessary* — strengthen the pin so `e` IS the chart map, which is
  a change to a STATEMENT, not a theorem, since the producer builds both from one source. A leaf
  that documents its own deletion route is worth more than one that documents only its proof.
