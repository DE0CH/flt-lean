## "NEEDS THE MATE/BECK–CHEVALLEY MACHINERY" IS ALMOST ALWAYS WRONG — the composite adjunction's `homEquiv` does it in ten lines
(2026-08-02, `flt-lean-44`, closing `exists_modPullback_of_locally_modPullback` in
`ModularCurve/RelativePicard.lean` — BLR 8.1/4, descent of "is a pullback from the base"
along a morphism with `π_*𝒪 = 𝒪`.)
That leaf's docstring listed three inputs as genuinely missing at this pin, and the
inventory was ACCURATE — all three really were absent. Only the PRICING of one was
wrong, and it was the one that made the node look like a research project:
> 2. **compatibility of the counit with (1)** — the Beck–Chevalley/mate identity saying
> that the restriction of `ε` to `π⁻¹U` IS the counit for `π ∣_ U`. This is the one step
> with no obvious shortcut; `CategoryTheory`'s `mateEquiv`/`conjugateEquiv` are the tools.
**No mate machinery is needed, and neither is any comparison of two composite
adjunctions.** For `adj₁ : F ⊣ G` and `adj₂ : H ⊣ I`, apply `(adj₁.comp adj₂).homEquiv`
to `H.map (adj₁.counit.app M)`: the inner `homEquiv` turns it into
`ε¹_M ≫ η²_M` by naturality of `η²`, and the outer one collapses by the RIGHT triangle
identity for `adj₁`, leaving `G.map (adj₂.unit.app M)`. Undoing the equivalence gives
    H(ε¹_M) = (F ⋙ H)(G(η²_M)) ≫ (adj₁.comp adj₂).counit.app (H M)
in ARBITRARY categories, ten lines. At `F ⊣ G = π^* ⊣ π_*` and `H ⊣ I = j^* ⊣ j_*` this
IS the Beck–Chevalley factorisation of `ε` restricted to an open, with `G(η²_M)` the
base-change map. The two factorisations `j ≫ π = (π ∣_ U) ≫ U.ι` then have to be
compared only as PULLBACK functors, where `pullbackComp`/`pullbackCongr` suffice.
**And the composite counit is handled by a triangle identity, not by an iso of
adjunctions.** `isIso (adj.counit.app (F.obj B))` follows from `IsIso (F.map (adj.unit.app B))`
by the LEFT triangle identity alone. Take `B = 𝒪_T`: `Lᶜ(𝒪_T) = j^*π^*𝒪_T ≅ 𝒪_{π⁻¹U}`,
and `ηᶜ_{𝒪_T} = η^π_{𝒪_T} ≫ π_*(η^j_{π^*𝒪_T})` (`Adjunction.comp_unit_app`) has both
factors iso after `Lᶜ`. So the whole "restrict the counit" step is two triangle
identities and a naturality square.
**The generalisable rule: when a route note prices a step at `mateEquiv`/`conjugateEquiv`
/ "compare the two composite adjunctions", first write the ADJUNCT of the map you want
and see what the triangle identities do to it.** A mate is by definition an adjunct; the
machinery exists to make mates natural in a 2-categorical sense, and a single instance of
one almost never needs it. Cost here: the entire leaf, three "missing" items and all,
came to ~460 lines, of which the mate step is 20.
Two riders from the same run, both reusable:
* **`SheafOfModules.unitToPushforwardObjUnit φ` has `val.app X a = φ.hom.app X a` by
  `rfl`** (`Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackFree.lean`), and
  `pullbackObjUnitToUnit` is its adjunct. So `AlgebraicGeometry.HasTrivialPushforward π`
  — a statement about the map of sheaves of RINGS, `∀ U, IsIso (π.app U)` — gives the
  MODULE-level `π_*𝒪_Z ≅ 𝒪_T` and `IsIso (η^π_{𝒪_T})` with no computation at all. This is
  the pushforward twin of the recorded `unitToPushforwardObjUnit_val_app_apply` trick for
  `sectionIdeal`; whenever a project object is an adjunction unit/counit at `𝒪`, look for
  the mathlib name before assuming its sections are opaque.
* **`Γ((pushforward f).obj M, U) = Γ(M, f ⁻¹ᵁ U)` and `Γ(M.restrict f, U) = Γ(M, f ''ᵁ U)`
  are both `rfl`**, so a base-change comparison between them is `M.presheaf.map` of an
  inclusion of opens, and it is an ISO exactly when that inclusion is an equality. Here
  `j ''ᵁ (j ⁻¹ᵁ W) = W` for `W ≤ π⁻¹U` — ONE topological identity
  (`Scheme.Hom.image_preimage_eq_opensRange_inf` plus `Scheme.Opens.opensRange_ι`) is the
  whole of "base change of `π_*` along an open immersion of the target".
### THE `(𝟭 C).obj` / `⋙` WRAPPER BREAKS `rw` **AND** INSTANCE SEARCH — carry a family of explicit-hypothesis helpers
This file already records that `adj.unit.app X : (𝟭 C).obj X ⟶ (F ⋙ G).obj X` is
`rfl`-equal and not syntactically equal to the unwrapped form, and that this breaks `rw`
and `Mono`-synthesis. Doing a whole adjunction argument makes the cure worth stating as a
recipe rather than as a case-by-case dodge. **Every one of these failed as instance
search and succeeded as an `exact`, so state each as a lemma taking the hypothesis or the
equation EXPLICITLY and apply it positionally:**
    isoOf (f) (h : IsIso f) : X ≅ Y                       -- `asIso` fails: synthInstance timeout
    isIso_comp_of f g (hf) (hg) : IsIso (f ≫ g)           -- `infer_instance` fails on a composite
    isIso_map_of_isIso F f (h : IsIso f) : IsIso (F.map f) -- `Functor.map_isIso` fails
    isIso_map_of_comp F (w : f ≫ g = u) (hf) (hg) : IsIso (F.map u)
    isIso_snd_of_comp_eq_id (w : f ≫ g = 𝟙 X) (hf) : IsIso g   -- `IsIso.of_isIso_fac_left` fails
    isIso_map_eqToHom F (h : X = Y) : IsIso (F.map (eqToHom h))
The last one is not a wrapper problem: **`IsIso (eqToHom h)` simply is not found by
instance search in `Ab`-valued presheaf categories** — it exhausts a 20 000-heartbeat
budget and does not succeed at 800 000 either. `subst h; rw [eqToHom_refl, F.map_id]` is
instant. And note `Functor.map_id` resolves to Lean core's `Functor` (the `Type → Type`
class) under `open CategoryTheory`; write `F.map_id`.
Three more measured details, each of which cost a round trip:
* **`rw [Functor.map_comp]` fails on a goal that prints correctly** — the reported pattern
  `G.map (?f ≫ ?g)` "is not found" because the composite is typed through the wrapper.
  A `calc` step closed by `G.map_comp _ _` as a TERM goes through. `simp` distributes it
  when the functors are bare variables and does not when they are project functors, so do
  not rely on it either way;
* **`have eW : W ≅ … := hsq.isoIsPullback _ _ hcan` FORGETS the definition** (the standing
  "`have` on DATA destroys defeq" rule), so `isoIsPullback_hom_fst`/`_snd` stop
  typechecking against it. Bind it with `obtain` from an `∃` carrying both fac equations;
* **`Adjunction.unit_leftAdjointUniq_hom_app` is the bridge between `restrictAdjunction f`
  and `pullbackPushforwardAdjunction f`** for an open immersion, because
  `Scheme.Modules.restrictFunctorIsoPullback` is by DEFINITION that `leftAdjointUniq`. Use
  `restrictAdjunction` wherever you must COMPUTE a unit on sections
  (`restrictAdjunction_unit_app_app` is `rfl`) and `pullbackPushforwardAdjunction`
  wherever you do adjunction ALGEBRA; the bridge costs one lemma application.
