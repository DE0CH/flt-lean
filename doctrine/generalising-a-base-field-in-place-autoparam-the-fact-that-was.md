## GENERALISING A BASE FIELD IN PLACE: autoParam the fact that was free, and check whether the morphism already determines the datum
(2026-07-31, `flt-lean-276`, generalising `EllipticScheme.lean`'s `ProjCoords` cluster from `ℚ`
to `F : Type u`.) Two techniques, both reusable, because this tree has several ℚ→field ports
still queued.
**A ℚ-only fact that a hundred call sites use IMPLICITLY becomes an `autoParam`, not a new
argument.** `ProjCoords.base_eq` — `ℚ →+* A` is a subsingleton — was consumed silently by
`add`, `add2`, `ext`, and by every one of the 58 `hom_ext_spec_rat` invocations. Adding
    (hb : c.base = d.base := by exact Subsingleton.elim _ _)
as the LAST binder leaves **every existing `ℚ` call site byte-identical** (the tactic fires and
finds `Rat.subsingleton_ringHom`) while a general-`F` caller gets a hard error until it supplies
the proof. The port becomes opt-in per call site and `ℚ` cannot regress. Two caveats, both hit:
* a `@[simp]` projection lemma ABOUT the autoParam'd definition must take the hypothesis as an
  explicit anonymous binder (`(h) (hb)`), because that lemma's own statement is elaborated at `F`,
  where the default tactic fails;
* what makes `rw`/`exact` still match a goal whose proof term came from the tactic rather than
  from the caller is proof irrelevance — so keep the hypothesis a `Prop`.
**Before threading a datum through, ask whether the MORPHISM already determines it.** The 58
`hom_ext_spec_rat` uses are not 58 obligations: they all sit in one position, the commuting square
of `Limits.pullback.lift c.toHom d.toHom _`. Two lemmas replace the lot:
* `ProjCoords.toHom_comp_projToSpec` — `c.toHom ≫ projToSpec E = X.toSpecΓ ≫ Spec.map (ofHom c.base)`,
  which is mathlib's `Proj.fromOfGlobalSections_toSpecZero` (it already exists — do not rebuild the
  chart dictionary for it) plus "`ringHom` evaluates a constant to itself";
* `ProjCoords.base_eq_of_toHom_eq` — the CONVERSE, `c.toHom = d.toHom → c.base = d.base`, because
  `Γ ⊣ Spec` is an adjunction (`Scheme.toSpecΓ_appTop`, `Scheme.Hom.comp_appTop`,
  `AlgebraicGeometry.ext_to_Spec`, `Spec.map_injective`).
The converse is what makes the port cheap: every rigidity/congruence lemma already knows
`c.toHom = c'.toHom`, so over `F` it needs **no new hypothesis at all**. The estimate that had
been carried in `MoretBailly.lean` for a year — "60 vanished justifications, the group-law port
crosses this obstruction dozens of times" — is right about the count and wrong about the cost.
**And for a PERVASIVE edit inside a monolith, the scratch module is a truncated PREFIX of the same
file.** The "verify in a scratch module" rule above assumes the new code is separable; when the
edit is spread over 3 000 lines of a 12 686-line file it is not. Write `lines[:N]` plus the
closing `end`s to `ScratchN.lean` — same imports, a quarter of the elaboration — and delete it
before committing (an unimported module under `Fermat/` is the fourth invisibility class).
Measured here: the clean file is **72 s**; a ~100-line prefix probing two lemmas is **60 s**; the
same full file carrying a dozen errors ran past **10 minutes**. **Error recovery, not size, is
what makes a broken monolith slow — never price the next round off the last one.**
