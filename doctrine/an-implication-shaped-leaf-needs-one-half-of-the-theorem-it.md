## AN IMPLICATION-SHAPED LEAF NEEDS ONE HALF OF THE THEOREM IT CITES — READ THE DIRECTION BEFORE PRICING IT
(2026-08-02, `flt-lean-207`, on `exists_narrowRayArtin_of_sup_eq_top` in
`Modularity/KhareWintenberger.lean`.) A leaf's docstring names a classical theorem, and the
theorem is an EQUIVALENCE or an ISOMORPHISM — Artin reciprocity, a universal property, a
kernel computation, "the map is bijective". The reflex is to price the whole theorem. **Ask
which direction the leaf's conclusion consumes**, because an implication-shaped conclusion
routinely uses one inclusion and never the other, and the unused half is very often the half
the theorem is named after and where every classical proof spends its effort.
Here the leaf reads *"there are `L` and `τ` such that every `w` with `Frob_w = τ` lies in the
narrow ray class of `(a)`"*, and its ROUTE cites the existence theorem of class field theory
**plus** Artin reciprocity `ker Art = P_𝔪`. Unfolded against the Artin ideal symbol, the
conclusion is `Art(w) = Art((a)) ⟹ w ∼_𝔪 (a)` — i.e. exactly `ker Art ⊆ P_𝔪`, the
SEPARATION half. `P_𝔪 ⊆ ker Art`, reciprocity proper, is never used. And the Artin map
itself costs nothing: `exists_idealSymbolMonoidHom` (`NumberField/CyclotomicIdealSymbol.lean`,
PROVEN, pure Dedekind-domain theory) extends any function on height-one primes to a monoid hom
on `(Ideal R)⁰`, so `w ↦ Frob_w` becomes a hom on the ideal monoid with no reciprocity input
at all.
The check is mechanical and costs one careful read: **write the leaf's conclusion as an
implication between the two sides of the cited equivalence, and see which arrow you need.**
Then say so in the docstring — a citation narrowed from "theorem X" to "one inclusion of
theorem X" is a real reduction that no leaf count can show, and it is what stops the next
owner budgeting the whole chapter.
Same family as the entries above about audits pricing a route rather than a statement, with
the mis-pricing one level up: the *citation* is over-strong, not the *route*.
### Riders from the same run
* **A TOTALLY POSITIVE REPRESENTATIVE OF A RESIDUE CLASS IS ARITHMETIC, NOT GEOMETRY.** The
  reflex for "the class `x + 𝔣` contains a totally positive element" is a lattice-point
  argument (𝒪_F is full in `F ⊗ ℝ`, the positive cone contains large balls). It is three
  lines instead: pick a nonzero RATIONAL integer `N ∈ 𝔣` (`Ideal.absNorm_mem`, nonzero by
  `Ideal.absNorm_eq_zero_iff`) and take `x + N·m` for large `m : ℕ`. A rational integer
  shifts EVERY real embedding by the SAME amount, so one `m` serves all of them, and the
  only finiteness used is that there are finitely many infinite places (`Finite.exists_le`).
  No nonemptiness of the set of real places is needed either, so a totally imaginary `F`
  costs nothing. Both in-tree proofs of this fact use that shape; the geometric one is
  never necessary.
* **GREP YOUR INTENDED NAME, NOT ONLY THE CONCEPT — a file-local naming convention hides the
  twin.** `exists_totallyPositive_sub_mem_ray_class` was already PROVEN in
  `HardlyRamified/ModThree.lean`, in a module not in the target's import cone, and it did not
  turn up in any concept grep because that file suffixes ~30 support lemmas with `_ray_class`
  regardless of subject (there are `quad_trace_ray_class`, `abs_discr_le_discr_of_isIntegral_ray_class`
  …). What found it was the routine collision check on the name I was about to introduce.
  **Run that check before writing any helper**: it costs one `grep -rn` and it is the only
  thing that sees a twin whose name differs from yours by a house-style suffix.
* **A 28 000-line module can elaborate in three minutes.** `KhareWintenberger.lean` is
  `lake env lean`-clean in **176 s** with warm oleans, so the scratch-module doctrine's
  premise ("the round trip on this file is half an hour") is FALSE for it. Measure before
  planning around it — the release snapshot at `~/.flt-release-lake` makes the imports free
  whenever `git diff --stat $(cat ~/.flt-release-lake/sha) HEAD -- Fermat/` is empty, which
  it is immediately after a published release.
