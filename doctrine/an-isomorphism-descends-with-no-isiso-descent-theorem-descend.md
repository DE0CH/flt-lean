## AN ISOMORPHISM DESCENDS WITH NO `IsIso`-DESCENT THEOREM — DESCEND BOTH WAYS AND CANCEL THE EPIS
(2026-08-01, `flt-lean-181`, `IsBaseChangeOfGamma1.cancelLeft` in `ModularCurve/X1.lean`.)
That leaf's route note said, correctly, that cancelling an fpqc cover on the LEFT of a
base-change square "is descent and is NOT formal" — and then priced it at effective descent
of SCHEMES, or at least descent of `IsIso`, neither of which is in the pin. Neither is
needed, and the recipe is general:
1. **Only ever descend MORPHISMS.** Both objects already exist over the base — `d` is given
   and `m^* dY` is `exists_gamma1Datum_baseChange` — so what is owed is an ISOMORPHISM
   `d.E ≅ (m^* dY).E`, never a scheme.
2. **Cancelling on the RIGHT turns one square into two squares over the SAME cover.**
   `b.cancel δ` re-reads `d'` as a base change of `m^* dY` along `p`, so you hold
   `bp : IsBaseChangeOfGamma1 p d' d` and `bq : IsBaseChangeOfGamma1 p d' e`: two fpqc
   comparison maps out of ONE object. Both are base changes of `p`
   (`MorphismProperty.of_isPullback`), hence `EffectiveEpi` by subcanonicity of
   `fpqcTopology`.
3. **Descend each along the other**: `φ := EffectiveEpi.desc bp.map bq.map _`,
   `ψ := EffectiveEpi.desc bq.map bp.map _`.
4. **The two identities are EPI CANCELLATIONS, not descent.**
   `bp.map ≫ (φ ≫ ψ) = bq.map ≫ ψ = bp.map = bp.map ≫ 𝟙`, and `bp.map` is an epi, so
   `φ ≫ ψ = 𝟙`; symmetrically for `ψ ≫ φ`. `IsIso φ` follows with no descent theorem
   anywhere, and `IsPullback.of_vert_isIso` then makes the square over `𝟙` cartesian for
   free.
**Where the mathematics really goes is the COCYCLE, and it is worth isolating as its own
leaf.** `EffectiveEpi.desc` wants `g₁ ≫ bp.map = g₂ ≫ bp.map → g₁ ≫ bq.map = g₂ ≫ bq.map`,
and that — not the descent — is the only non-formal step. Cutting it out as
`IsBaseChangeOfGamma1.map_unique` (*two cartesian squares over the same `h` have the same
comparison morphism*, i.e. Katz–Mazur 2.7.2, `Aut` of a `Γ₁(N)`-datum is trivial for
`N ≥ 4`) left ~250 lines of pure descent PROVEN and a residue that is a one-line citation
mentioning no atlas, no coarse space and no base field. **A "this step is not formal"
verdict usually names a step that IS formal once its one non-formal input is named; find
that input and make IT the leaf.**
Two mechanical facts that carried the whole proof, both worth reaching for by default:
* **A structure field quantified over an arbitrary test object cannot be checked after the
  cover, and CAN be checked after the cover's BASE CHANGE.** `map_zero : ∀ {U} (g : U ⟶ T), …`
  is not reachable by `cancel_epi p`; but `U ×_T T' ⟶ U` is again flat surjective
  quasi-compact — `MorphismProperty.of_isPullback` at `(IsPullback.of_hasPullback g p).flip`
  — hence an epi, and `AbelianSchemeStruct`'s two NATURALITY FIELDS (`pre_zero`, `pre_add`)
  are exactly what moves the points across. Nothing else about the abelian scheme is used,
  and `add_val_congr` absorbs every base-point identification.
* **A base-change square is indexed by its base morphism, so propositionally-equal
  composites carry squares of different TYPES.** Name the transport (`congrHom`) and prove
  `congrHom_map` (`by subst hh; rfl`) ONCE: the `map` field does not mention the index, so
  after that every step runs on underlying morphisms where no index is visible. Without it
  `rw` on the index hits `motive is not type correct` at every turn.
### `rw` FAILS ON `RelPoint.along`/`RelPoint.pre` — THE GOAL BETA-REDUCES AND THE LEMMA DOES NOT
Three of the six iterations went here, and the symptom is the standing one in its most
misleading form. `congrArg Subtype.val (bp.map_add x y)` has type
`↑(RelPoint.along bp.map _ (d'.ab.add x y)) = …`, while the goal — after `Subtype.ext` and
a `cancel_epi` — carries the beta-reduced `↑(d'.ab.add x y) ≫ bp.map`. They are DEFEQ and
not syntactically equal, so `rw` reports *"Did not find an occurrence of the pattern"*
against a pattern that is visibly present in what it prints. **State the reduced form as an
explicit `have` and build it with `Eq.trans`/`exact`**, which check up to defeq; every later
`rw` then matches. Same for `RelPoint.pre h hg x`, whose `.1` is `h ≫ x.1`.
And when `rw [Category.assoc]` reports `motive is not type correct` naming a term you did
not think was involved, it has matched the associativity pattern **inside the TYPE of
something in the goal** — here `(g₁ ≫ d'.f) ≫ p` inside a base-change square's index.
Either give `Category.assoc` all three explicit arguments, or `obtain` the offending
morphism as an opaque variable carrying only its characterising equations; the second is
what finally worked, and it is the same "bind it, do not retype it" move recorded elsewhere
in this file.
**Accounting, stated the way the RECUT rule asks**: the direct-sorry count went `1 → 2`
(`X1.lean` 24 → 25). That is disclosure: one leaf carrying the whole of Katz–Mazur 4.7.1
became a CONSTRUCTION (build one scheme and one cartesian square at one named morphism) and
a CITATION (2.7.2) that is base-generic, universe-polymorphic and reusable by `X0.lean`.
Judge it by what is LEFT in each leaf.
