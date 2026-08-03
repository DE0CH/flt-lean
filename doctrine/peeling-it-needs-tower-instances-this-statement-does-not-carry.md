## "PEELING IT NEEDS TOWER INSTANCES THIS STATEMENT DOES NOT CARRY" — THE INSTANCES CAN LIVE IN THE PROOF

(2026-08-01, `flt-lean-329`, on `exists_baseChangeHeckeField_of_prime_cyclic_step_of_inert`
in `Modularity/KhareWintenberger.lean`.)  A leaf that bundles a citation with an
elementary side condition routinely carries a docstring naming the peel and
declining it, in this shape:

> The place clause is elementary and would be the natural NEXT CUT … That is
> ordinary ramification theory and needs no automorphic input; **it is left here
> only because peeling it requires the `L/M` tower instances, which this
> statement deliberately does not carry.**

That sentence conflates two different things, and only the first is true: the
PROOF needs the tower instances, the STATEMENT does not.  Here the tower is
`M = F^D ⊆ F^C = L` for `C ≤ D` subgroups of `Gal(F/ℚ)`; the peeled theorem is
stated over `Subgroup (Φ ≃ₐ[ℚ] Φ)` and the two fixed fields — **exactly the
vocabulary the leaf already uses** — and every instance (`Algebra ↥M ↥L`,
`IsScalarTower`, `Normal`, `IsGalois`) is introduced by `letI`/`haveI` inside the
proof body.  No consumer pays for any of them, and the peel landed as a
mathlib-facing module with a two-line assembly at the leaf.

**The check is one question: does the CONCLUSION mention the missing structure?**
If the conclusion can be phrased with the objects the leaf already quantifies
over — here `Finset (HeightOneSpectrum (𝓞 ↥(fixedField C)))` and `absNorm` — then
the instances are proof-local and the "statement does not carry them" objection
is answered by construction.  The objection is real only when the missing
structure appears in the STATEMENT.

**The mechanism that makes it work, and it is reusable for any pair of
intermediate fields.**  `IntermediateField.extendScalars (h : E ≤ F) :
IntermediateField ↥E L` has `↥(extendScalars h)` **DEFEQ** to `↥F` (verified by
`rfl`), so

    letI : Algebra ↥(fixedField D) ↥(fixedField C) :=
      inferInstanceAs (Algebra ↥(fixedField D) ↥(extendScalars (fixedField_le hCD)))

gives the algebra structure ON THE ORIGINAL TYPE, and the same `inferInstanceAs`
gives `IsScalarTower`.  There is NO `Algebra ↥E ↥F` instance for `E ≤ F` in the
pin — checking that is what makes the docstring's objection sound — but there does
not need to be.

Two further pieces this needed, both already in the pin and both easy to price as
missing:

* **`IsGalois M L` from `(C.subgroupOf D).Normal`** is `IntermediateField.
  normal_iff_forall_map_le'` plus three lines of conjugation: a `Φ ≃ₐ[M] Φ`
  restricts into `D` (`IntermediateField.fixingSubgroup_fixedField`), and
  normality gives `σ⁻¹ τ σ ∈ C`, so `σ` preserves `fixedField C`.  Separability is
  free in characteristic zero, so `Normal` upgrades to `IsGalois` by `⟨⟩`.
* **the fundamental identity for a Galois extension** is
  `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`
  (`Mathlib/NumberTheory/RamificationInertia/Galois.lean`), `g·(e·f) = Nat.card G`,
  with `Ideal.inertiaDegIn_eq_inertiaDeg` to read `f` off a chosen prime and
  `Ideal.absNorm_pow_inertiaDeg` to convert to norms.  **The `𝓞`-level
  `IsGaloisGroup` instance is automatic for number fields** (`FieldTheory/Galois/
  IsGaloisGroup.lean` registers `IsGaloisGroup G (𝓞 K) (𝓞 L)`), so nothing has to
  be transported by hand — the whole abstract lemma is 15 lines.

**And say GALOIS is load-bearing where it is.**  Without it the identity is only
`∑_{v|w} e_v f_v = p`, which at `p = 5` admits `(e,f) = (1,2)` and `(1,3)`: both
have `f ≥ 2` and neither has `f = p`.  It is uniformity of `f` across `v | w` that
forces `g = 1`.  A reader who sees only `∑ e f = p` will think the hypothesis is
decoration.

**Accounting, in the shape the RECUT rule asks for: the count did not move, `1 -> 1`.**
What changed is that the surviving leaf is PURELY the Arthur–Clozel citation —
its conclusion lost a conjunct that was ordinary ramification theory, and a
successor no longer has to know what a `HeightOneSpectrum` is to attack it.  The
old name and its exact statement survive as a PROVEN assembly, so the consumer did
not move and no queue entry naming it went stale.

**Inheritance of the audits is immediate here, and worth saying why.**  This recut
only DELETED a conjunct from the CONCLUSION, so the leaf is strictly WEAKER than
the statement its (long, correct, `ζ`-torsor) audits were written against — every
counterexample to the new leaf is one to the old.  I also RETAINED the now-unused
hypothesis `∀ v ∉ SL, Nv ≠ Nw`: it costs a prover nothing and it is what makes the
"strictly weaker" claim, hence the inheritance, hold without an argument.

### `set_option … in` / `open … in` ABOVE THE DOC COMMENT — this fired TWICE in one run

CLAUDE.md already records it, and it still cost two build cycles here — once on a
30-second module, once on a **19-minute** one.  The error is
`unexpected token 'set_option'; expected 'lemma'` (or `'open'`), reported at the
END of the docstring, which reads like a problem with the comment.  The modifier
combinator takes the WHOLE declaration, docstring included, so it goes ABOVE the
`/--`.  When a script GENERATES the declaration, that is where the bug lands,
because the natural template is `docstring + modifier + theorem`.  Grep for
`-/\n(set_option|open|omit|attribute).* in$` after any scripted insertion; it is
one command and it is cheaper than a giant-module rebuild.

