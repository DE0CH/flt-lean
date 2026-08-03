## WHEN A LEAF'S ROUTE ASKS FOR `Ω` OF A GROUP SCHEME, GREP FOR THE TANGENT SPACE INSTEAD — the two are one theorem and only one of them is in this tree
(2026-08-01, `flt-lean-298`, closing `kaehler_stalkMap_mulByNat_prime_eq_zero` in
`Modularity/TateModule.lean`.)  That leaf carried a three-screen docstring pricing it at
the classical argument — *`Ω_{A/k}` is FREE on the invariant differentials, and `f ↦ f^*`
is ADDITIVE on them, so `[p]^* = p = 0`* — which is a correct proof and a large one: a
sheaf of differentials for a group scheme, the translation action, and the freeness
theorem, none of which this pin has.  The whole crux was **already PROVEN, five thousand
lines away, in a module this one already imports, under a name sharing no keyword with
the leaf**: `nonempty_module_infKernel_of_squareZero`
(`Modularity/AbelianSchemeIsogeny.lean`, 2026-07-27) — *for a square-zero thickening
`Spec R₀ ⟶ Spec R`, the kernel `ker (A(R) ⟶ A(R₀))` is a `k`-VECTOR SPACE*.
That IS "the tangent space is a module and `[n]` acts on it by `n`", i.e. exactly what
freeness-plus-additivity is for.  Its own docstring says so, in a paragraph headed
**A GENERALISATION THAT IS ALSO TRUE**: *"the classical isomorphism
`ker(G(R) ⟶ G(R₀)) ≅ Hom_{R₀}(e^* Ω_{G/S} ⊗ R₀, ker φ)` … is valid for every group
scheme"*, and *"the proof below never constructs `Ω`"*.  Given it, the leaf is
bookkeeping: take the thickening to be the UNIVERSAL one,
`𝒪_{A,x} ⊕ Ω[𝒪_{A,x}⁄k] ↠ 𝒪_{A,x}`, whose two sections are `r ↦ (r, d r)` and
`r ↦ (r, 0)`; they are two `Spec`-points with the same restriction, so their difference
is killed by `p`, so `[p]` does not separate them, so `d` kills the image of `[p]^{\#}`.
About 200 lines, and `#print axioms` comes back `[propext, Classical.choice, Quot.sound]`.
**Why no ordinary check finds it, and what does.**  The leaf's vocabulary is `kaehler`,
`stalkMap`, `mulByNat`, `differential`, `invariant`; the theorem's is `infKernel`,
`squareZero`, `module`.  A grep on either side returns nothing of the other, and both
docstrings are long and careful.  What links them is the MATHEMATICAL CONTENT stated in
prose.  So: **when a route asks for differentials of a GROUP object, grep for
`tangent`, `Lie`, `infKernel`, `squareZero`, `Der`, `dual number` — and conversely.**
`Ω` of a group scheme and its tangent space at the identity are the same datum, and a
development formalises whichever of the two its first consumer happened to need.
Two riders, both general:
* **This is the fourth distinct place the standing rule fires** (after
  `flt-inventory-audits-understate-what-exists`, "missing machinery may be DOWNSTREAM",
  and "check your own import list first"), and the new coordinate is UPSTREAM AND FAR:
  the theorem was in an already-`public import`ed module, thousands of lines from
  anything the leaf mentions.  "Reachable" was never the problem; NAMEABLE was.
* **A leaf's own docstring predicted its own unused hypothesis correctly and its own
  route wrongly.**  The paragraph headed **`hp` IS NOT CONSUMED** was exactly right —
  primality is nowhere in the proof.  The paragraph headed **THE CLASSICAL PROOF** was a
  cost hypothesis written before anyone tried.  A docstring is reliable about what it
  observed and unreliable about what it predicted; sort its paragraphs that way.
### Four Lean traps met on the way, each worth a round trip
* **`X.fromSpecStalk x` is a MONO, so cancelling it is two lines.**  Mathlib registers
  `instance [IsPreimmersion f] : Mono f` and an `IsPreimmersion` instance for
  `fromSpecStalk`, so `Spec.map a ≫ X.fromSpecStalk y = Spec.map b ≫ X.fromSpecStalk y`
  gives `a = b` by `(cancel_mono _).mp` then `Spec.map_injective`.  **Do not reach for
  `SpecToEquivOfLocalRing`** — it needs `IsLocalRing` on the source and `IsLocalHom` on
  the map, neither of which you will have for a square-zero extension unless you prove
  them.
* **Make the carrier type an EXPLICIT argument of any helper `def` you will instantiate
  at `↥(X.presheaf.stalk x)`.**  With it implicit, unification unfolds `Presheaf.stalk`
  to its colimit and then searches for `Algebra k ↑(Limits.colimit.cocone …)`, which no
  `letI`, `variable` or instance binder in the stalk's own spelling will match.  The
  error reads as a missing instance and is a unification accident; the same happens with
  `set R := X.presheaf.stalk x`, which this file already records for ideals.
* **`variable [CommRing k]` in a section plus `[Field k]` on a theorem is a real
  diamond, and `stalkAlgebraOver` is where it bites.**  `letI : Algebra k ↥(stalk) :=
  stalkAlgebraOver aX x` then FAILS to typecheck, reporting
  `CommRing.toCommSemiring` against `Field.toSemifield.toCommSemiring` — two independent
  instances, not two paths to one.  `linter.overlappingInstances` warns about it in as
  many words; obey the warning rather than routing around it.  Use ONE of the two
  everywhere.
* **`Module Rᵐᵒᵖ M` is NOT an instance for a commutative `R` and an `R`-module `M`**, so
  `TrivSqZeroExt R M` is not even a ring until you supply it:
  `Module.compHom M ((RingHom.id R).fromOpposite fun x y => mul_comm x y)` plus
  `IsCentralScalar R M := ⟨fun _ _ => rfl⟩`.  **Declare both `local`**: at `M = R` a
  global version is a rival of mathlib's own `Module Rᵐᵒᵖ R`.  Everything whose
  STATEMENT mentions `TrivSqZeroExt R M` is then confined to that section — which is
  fine, and is a reason to make sure the statements you want to export (here the crux
  and its instantiation) do not mention it.
