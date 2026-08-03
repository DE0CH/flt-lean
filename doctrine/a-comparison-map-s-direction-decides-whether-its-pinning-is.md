## A COMPARISON MAP'S *DIRECTION* DECIDES WHETHER ITS PINNING IS FREE — build maps OUT of the sheafification
(2026-08-01, `flt-lean-13`, closing `exists_restrict_modTensor_tensorSection`, the one live
leaf of `Modularity/AmpleSheaf.lean`.)
This development is full of leaves of the shape *"there is an isomorphism `A ≅ B`, PINNED by
its effect on `tensorSection`/`modPullbackSection`/`trivializedSection`"*, and the file
already records that a bare `Nonempty (A ≅ B)` is under-pinned and must be replaced by such a
clause. What it does not record, and what decides the cost of every one of them, is that
**the two directions of the SAME isomorphism have completely different prices, and the leaf's
own docstring usually fixes the expensive one.**
The rule: **a map OUT of a sheafification (or any object given by a left adjoint / universal
property) is supplied BY that universal property from presheaf data, so its value on the
generators is true by construction — at EVERY object of the site, with no transport. A map
INTO one is not, and every route to its values goes through a unit whose components are
`presheaf.map (homOfLE …)` between opens that are only PROPOSITIONALLY equal.**
Concretely here. The leaf asks for `e : (L ⊗ M)|_W ≅ L|_W ⊗ M|_W` with `e.hom` pinned. Its
docstring, and three separate route audits in the same file, prescribed transporting the
proven pullback comparison along `modRestrictPullbackIso`. That route dies for a reason that
is invisible until you write it: `modPullbackTensorComparison_tensorSection` is stated at `⊤`
and the bridge to a section over `W` is `(restrictAdjunction f).unit`, whose value at `V` is
`A.presheaf.map (homOfLE (f.image_preimage_le V)).op` — the identity only up to
`f ⁻¹ᵁ (f ''ᵁ U) = U`, which is **not** definitional. The leaf quantifies over ALL sections
over `W`, not just restrictions of global ones, so the transports cannot be dodged.
Built in the OTHER direction — `d : L|_W ⊗ M|_W ⟶ (L ⊗ M)|_W`, whose SOURCE is the
sheafification — the pinning is three lines (`Equiv.apply_symm_apply`,
`Adjunction.homEquiv_unit`, and the presheaf map's value on a pure tensor), holds at EVERY
open for free, and the leaf is `d` inverted. **So when a leaf names a direction, check which
side is the colimit/sheafification and prove the other-direction statement first.**
### The `IsIso` half is two mathlib facts and one piece of algebra, and none of it is geometry
The leaf's docstring called the residue *"sheafification commutes with restriction to an open
subsite"* and priced it as a covering-sieve argument to be written by hand. It is not:
* **`f.opensFunctor.IsCocontinuous` is a mathlib INSTANCE for every open immersion**
  (`Mathlib/AlgebraicGeometry/OpenImmersion.lean`), and
  `Mathlib/CategoryTheory/Sites/PreservesLocallyBijective.lean` carries
  `Presheaf.isLocallySurjective_whisker` / `isLocallyInjective_whisker`. Together they
  transfer local bijectivity of `modTensorMk` (which is `toSheafify`) from `Opens Y` to
  `Opens X` with **nothing to prove**. Neither file is reachable by grepping for
  "sheafification" or "restriction"; find them by grepping for `IsCocontinuous`.
* **`PresheafOfModules.pushforward₀OfCommRingCat` is MONOIDAL with `μIso = Iso.refl`**
  (`Presheaf/PushforwardZeroMonoidal.lean`), so precomposition with a functor contributes
  nothing. The ONLY comparison map in sight comes from the `restrictScalars` half.
* That `μ : A ⊗_R B ⟶ A ⊗_S B` is bijective **as soon as `φ : R → S` is SURJECTIVE** — not
  merely an iso, which is what one reaches for. Surjectivity of `μ` is free for any `φ`;
  INJECTIVITY is `TensorProduct.liftAddHom` applied to `(a, b) ↦ a ⊗ₜ[R] b`, whose balanced
  condition `(s • a) ⊗ₜ b = a ⊗ₜ (s • b)` is exactly where `s = φ r` is spent. ~40 lines, and
  it is a general change-of-rings statement worth stating separately.
**The generalisable check: before pricing a sheaf-theoretic leaf as a site argument, ask
which of its steps mathlib states as a property of a FUNCTOR** (`IsCocontinuous`,
`IsCoverDense`, `CoverPreserving`, `HasSheafCompose`). Those come with instances; the
hand-rolled sieve version of the same fact is 100 lines.
### Re-declare an anonymous `letI`-bound datum verbatim, and the whole mathlib API opens up
`Scheme.Modules.restrictFunctor f` is `SheafOfModules.pushforward` along `f.opensFunctor`
with a ring map `α` bound by a `letI` INSIDE the definition — so it has no name and cannot be
cited. Re-declaring it verbatim in your own file (`restrictAlpha`, four lines; its naturality
is `Scheme.Hom.appIso_inv_naturality`, which mathlib discharges with `cat_disch` and which
does not fire outside that file) makes
    (L.restrict f).val = (PresheafOfModules.pushforward (restrictPhi f)).obj L.val
hold by **`rfl`**, and with it every lemma mathlib proves about `pushforward` becomes usable —
including `pushforwardCompToPresheaf` being `Iso.refl`, which is what makes
`toPresheaf.map ((pushforward φ).map g) = whiskerLeft f.opensFunctor.op (toPresheaf.map g)`
a `rfl` and lets the whisker lemmas above apply on the nose. **Whenever a mathlib definition
you need to reason about binds its data with `letI`/`let` rather than naming it, re-declare
that data rather than working around it**; the cost is one definition and the payoff is
definitional compatibility with the entire surrounding API.
Three smaller traps, each one round trip:
* **`ConcreteCategory.hom` coercions defeat `rw` on `map_zero`/`map_add`** when the domain
  and codomain are defeq-but-not-syntactic (`↑((restrictScalars φ).obj (A ⊗ B))` versus
  `↑A ⊗[S] ↑B`). The cure is to state the instance you want as a `have` (`have h0 : m0 0 = 0
  := map_zero _`) and `rw [h0]` — the `have`'s statement elaborates at the goal's own types.
* **A coercion `(m : A')` between defeq `ModuleCat` carriers does not retype `m`**, so
  `TensorProduct.smul_tmul r (m : A') (n : B')` still elaborates at `↑A` and fails to
  synthesize `Module R ↑A`. Introduce the fact as a `have key : ∀ (x : A') (y : B'), …` and
  apply it; the binders force the types.
* **An instance declared in a mathlib section whose variables include a datum your goal does
  not mention will not be found.** `(SheafOfModules.toSheaf R).ReflectsIsomorphisms` is
  declared under `(α : R₀ ⟶ R.obj)` plus its local-bijectivity hypotheses, so `α` is a
  metavariable at the use site and search does not fire. Replicating mathlib's own two-line
  proof locally (`reflectsIsomorphisms_of_comp _ (sheafToPresheaf _ _)`) is the fix.
