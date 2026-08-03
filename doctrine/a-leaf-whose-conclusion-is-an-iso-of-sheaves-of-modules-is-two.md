## A LEAF WHOSE CONCLUSION IS AN ISO OF SHEAVES OF MODULES IS TWO LEAVES — AND THE SHEAF HALF IS PROVABLE ONCE, GENERICALLY

(2026-07-31, `flt-lean-278`, `exists_trivialization_sectionIdeal_at_section` in
`ModularCurve/RelativePicard.lean`.)  The section above says to recut a `Nonempty (A ≅ B)`
leaf as `IsIso <named map>`.  There is a stronger move available whenever the leaf's real
content is GEOMETRY and its conclusion is stated in `Z.Modules`: **the whole sheaf-theoretic
half — build the map, factor it through the kernel, check `IsIso` on sections — is provable
with NO geometric hypothesis at all, and it should be, once, so that the residue is a
statement about ring sections.**

Here the leaf was "near `σ(t)` the ideal sheaf `𝒪(−σ)` is `≅ 𝒪_U`", carrying `IsProper`,
`SmoothOfRelativeDimension 1` and `σ ≫ strY = 𝟙`.  It is now PROVEN over

    exists_generator_sectionIdeal_at_section :  ∃ U ∋ σ(t), ∃ s ∈ Γ(Y, U),
        σ.app U s = 0                                                    -- s is in the ideal
      ∧ (∀ W ≤ U, ∀ r, r * s|_W = 0 → r = 0)                             -- s is a nonzerodivisor
      ∧ (∀ W ≤ U, ∀ x, σ.app W x = 0 → ∃ r, x = r * s|_W)                -- s generates it

plus a hypothesis-free `nonempty_sectionIdeal_restrict_iso_of_generator`.  Count `1 → 1`; what
left the leaf is ~250 lines of `SheafOfModules` category theory that every successor would
otherwise have rebuilt, and the residue mentions no kernel, no adjunction and no `modUnit`.

**THE ONE IDENTIFICATION THAT MAKES THE CUT EXPRESSIBLE — and it generalises past this
file.**  `sectionIdeal σ` is `ker` of the `σ^* ⊣ σ_*` unit, so its sections look
unreachable.  They are not: the unit composed with `σ_*(σ^*𝒪 ≅ 𝒪)` **is** mathlib's
`SheafOfModules.unitToPushforwardObjUnit`, whose value on sections is `σ^♯` **by `rfl`**
(`unitToPushforwardObjUnit_val_app_apply`), and the second factor is an iso hence injective.
So `Γ(ker unit, W) = ker (σ.app W)` in three lines.  `RelativePicard.lean` already used
exactly this route for the generic point (`toConstSheaf_eq`) and nobody had noticed it applies
to every `σ`.  **Whenever a project object is defined as a kernel/cokernel of an adjunction
unit or counit, look for the mathlib name of that unit before assuming its sections are
opaque.**

Five mechanical facts that cost most of the session and are reusable for anything touching
`X.Modules`:

* `Γ((U : Scheme), V) = Γ(Z, U.ι ''ᵁ V)` and `Γ(M.restrict U.ι, V) = Γ(M, U.ι ''ᵁ V)` are
  **`rfl`**, and so is `Hom.app ((restrictFunctor U.ι).map φ) V = Hom.app φ (U.ι ''ᵁ V)`.  So
  restriction to an open costs nothing at the level of sections;
* `Scheme.Modules.restrictUnitIso U.ι` is the **identity** on sections (its component is
  `U.ι.appIso`, and `Scheme.Opens.ι_appIso : U.ι.appIso V = Iso.refl _`).  Proving that is a
  two-line `simp`; using it needs `congrArg`, not `rw` (next bullet);
* **`rw` fails on `Hom.app (restrictUnitIso _).inv V` with the pattern visibly present in the
  goal**, reporting "the target expression is not type-correct under the `instances`
  transparency level" — because `(modUnit Z).restrict U.ι` presents its presheaf as a
  `TopCat.Presheaf`.  `congrArg (fun m => ConcreteCategory.hom m y) h` followed by
  `Eq.trans` crosses it.  This is the standing "printed pattern equals printed target ⟹
  switch to a defeq-checking tactic" rule, with a new cause;
* **`AddCommGrpCat.injective_of_mono` is `Type 0` ONLY** (`Function.Injective.{1,1}`), which
  is useless at `Ab.{u}`.  The universe-polymorphic one is
  `ConcreteCategory.injective_of_mono_of_preservesPullback`.  And to make instance search find
  the `Mono` you supply, state it in the goal's own shape (`Mono (Hom.app f V)`) and open it
  with `show Mono ((modSectionsAt _ V).map f)`, not the other way round;
* **a type ascription `(a : Γ(Z, W))` on an element of a DEFEQ-but-different type does not
  retype it** — you get `failed to synthesize HMul ↑Γ(modUnit ↑U, V) ↑Γ(Z, …)`.  Fix it at the
  STATEMENT: after `rw [ConcreteCategory.isIso_iff_bijective]`, do
  `show Function.Bijective (fun x : Γ(Z, U.ι ''ᵁ V) => ConcreteCategory.hom … x)`.  `show`
  crosses the defeq once and every element below is then a ring element.

Corollary for how to price such a leaf: **the sheaf half is a fixed cost that does not depend
on the geometry, so it is worth paying even when you cannot touch the geometry at all.**  The
frontier does not move, and that must be said in the commit — a `−1 +1` delta is
indistinguishable from "nothing happened".

