## IN A BALANCED CATEGORY, `Mono` IS THE HALF WORTH SHOPPING FOR — AND IT CAN BE CHEAPER THAN THE `Epi` YOU WERE GIVEN
(2026-08-02, `flt-lean-70`, closing `isIso_of_epi_of_isInvertibleSheaf` in
`ModularCurve/RelativePicard.lean`.) That leaf — *a surjection of invertible sheaves is an
isomorphism* — carried a fully worked route whose one non-formal step was
**`Epi ⟹ locally surjective` for `Z.Modules`**, and the docstring was right that this is
real work: `Sheaf.isLocallySurjective_iff_epi` and `isLocallySurjective_iff_epi'` are about
`Sheaf J (Type w)` / `Sheaf J A`, and getting from `Z.Modules` to either needs
`SheafOfModules.toSheaf` to preserve epis, i.e. its exactness, which the pin does not state.
The same docstring also recorded, in bold, the route NOT to retry: *"`Z.Modules` is abelian,
so `Epi` plus `Mono` gives `IsIso`, and one hopes `Mono` is formal. It is not — `Mono` is
exactly the injectivity the flat-base-change route was for."* **The first clause is right and
the verdict is wrong.** `Mono` is not formal, but it is ELEMENTARY, and — this is the part
that inverts the whole cost model — **it comes out of the `Epi` hypothesis itself**, not out
of invertibility:
* `SheafOfModules.unitHomEquiv` makes an endomorphism of `𝒪_Y` multiplication by a section,
  and `End(𝒪_Y)` COMMUTATIVE (two lines each);
* so `Epi g` may be cancelled against the *multiplication* maps `modUnitMul a`, and that
  cancellation IS injectivity of `g.app ⊤`. No covering sieve, no sheafification, and no
  naturality of `g` — the compatibility a local argument would have to arrange by hand is
  carried for free by `PresheafOfModules.sections`, whose elements are compatible families
  and are therefore determined by their value at `⊤` (three lines from `s.property`);
* `restrictFunctor` is a left adjoint, so `Epi` restricts, and rerunning that on each open
  gives injectivity everywhere, hence `Mono`, hence `IsIso` by `isIso_of_mono_of_epi`.
**The generalisable move: when a leaf's conclusion is `IsIso` in an ABELIAN category and one
of `Mono`/`Epi` is a hypothesis, price the OTHER one before pricing the route's local
argument.** The classical proof extracts a local inverse from surjectivity; the Lean proof
extracts a global non-zerodivisor from cancellability and lets `Balanced` supply the inverse.
The second needs strictly less machinery, and in this instance it also deleted the "shrink
the trivializing open from `U` to `V`" step, which would have cost the
composition-of-restrictions bookkeeping.
**Corollary about `Epi` as a hypothesis.** An `Epi` in the binder list is usually read as
"the hard half is done, now do the other half". It is also a *supply* of cancellations
against any morphism you can name — and when the object is a unit object, `unitHomEquiv`
names them all. Ask what `Epi` GIVES before asking what it leaves to do.
### THE TYPE FRICTION THAT DECIDES WHETHER ANY OF THIS ELABORATES: `Γ(modUnit Y, X)` vs `Γ(Y, X)`
Same run, and it cost half the iterations until it was seen. `Γ(modUnit Y, X)` is an `Ab` and
`Γ(Y, X)` is a `CommRingCat`; their CARRIERS are defeq and Lean will not unify them while
elaborating a `*`. So `Scheme.Modules.Hom.app g X y * r` typechecks (the ring factor is on the
right and drags the unifier), `r * Scheme.Modules.Hom.app g X y` does NOT
(`failed to synthesize HMul ↑Γ(Y, X) ↑Γ(modUnit Y, X) ?`), and — per the standing rule — an
inline ascription `(… : Γ(Y, X))` does not retype it either.
**What does work is a `def` whose DECLARED type is the ring one:**
    noncomputable def gsec (g : modUnit Y ⟶ modUnit Y) (X : Y.Opens) : Γ(Y, X) :=
      Scheme.Modules.Hom.app g X (1 : Γ(Y, X))
The body has type `Γ(modUnit Y, X)`; the declaration is accepted by defeq; and from then on
`gsec g X` is a genuine ring element, so every downstream `mul_comm`/`one_mul`/`ring` step
elaborates with no friction at all. **One ascription at a definition beats an ascription at
every use site** — this is the cheap general remedy whenever two categories share a carrier.
Related and confirmed by `rfl` here: `r • (z : Γ(modUnit Y, X))` IS `(r * z : Γ(Y, X))`, so
`Hom.app_smul` is the linearity lemma to reach for and `•` is the well-typed spelling.
And the standing `rw` warning applies in a new place: any goal mentioning
`(modUnit W).presheaf` is not type-correct at `instances` transparency (it presents as a
`TopCat.Presheaf`, not as a functor out of `(Opens W)ᵒᵖ`), so `rw` fails on patterns that
print identically to the target. Every such step in this development must be `exact`, `show`,
`congrArg` or `ConcreteCategory.congr_hom`. The cheapest structural dodge is to state the
lemma so the isomorphism is a HYPOTHESIS rather than a term you must compute the sections of
— `injective_app_top_of_epi_of_iso_modUnit` takes `e : M ≅ modUnit Y` precisely so that no
caller ever has to evaluate `Scheme.Modules.restrictUnitIso` on sections.
