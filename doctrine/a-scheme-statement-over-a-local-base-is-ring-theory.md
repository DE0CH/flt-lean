## A SCHEME STATEMENT OVER A **LOCAL** BASE IS RING THEORY — `SpecToEquivOfLocalRing` is the whole dictionary

(2026-07-31, `flt-lean-287`, closing `eq_of_formalImmersionAt` in `MazurTorsion.lean`.)

Whenever a leaf quantifies over morphisms **out of `Spec` of a LOCAL ring** — sections of
an integral model over `Spec ℤ_(q)`, tangent vectors `Spec 𝔽_q[ε] ⟶ X`, residue points
`Spec 𝔽_q ⟶ X` — the entire statement can be moved to commutative algebra over ONE stalk,
with no charts, no affine covers and no gluing. The pin has the dictionary:

* `AlgebraicGeometry.SpecToEquivOfLocalRing X R : (Spec R ⟶ X) ≃ Σ x, {f : 𝒪_{X,x} ⟶ R // IsLocalHom f}`
  (`Mathlib/AlgebraicGeometry/Stalk.lean`), with `Scheme.Spec_stalkClosedPointTo_fromSpecStalk`
  and `Scheme.stalkClosedPointTo_comp` as its two computation rules;
* `AlgebraicGeometry.Scheme.Spec_closedPoint` — a **local** ring map sends the closed point
  to the closed point, which is what identifies the point all four objects sit over;
* `Scheme.SpecMap_stalkMap_fromSpecStalk` — how `fromSpecStalk` moves along a morphism.

The three moves that make it mechanical, and they are worth memorising:

1. **Fix the point once.** Get `hp : x.base (closedPoint R) = p` from the reduction
   hypothesis, then factor EVERY morphism as `Spec.map θ ≫ X.fromSpecStalk p`. The helper
   that makes this painless takes `p` as a **variable** so `subst hp` works:

       theorem exists_stalkHom (f : Spec (.of S) ⟶ X) {p : X} (hp : f.base (closedPoint S) = p) :
           ∃ θ : X.presheaf.stalk p ⟶ .of S, IsLocalHom θ.hom ∧ Spec.map θ ≫ X.fromSpecStalk p = f

   Doing it without that indirection means fighting `stalkCongr`/`▸` transports all day.
2. **Precomposition with `Spec.map ν` is postcomposition with `ν` on the ring side**:
   `Spec.map ν ≫ (Spec.map θ ≫ fromSpecStalk p) = Spec.map (θ ≫ ν) ≫ fromSpecStalk p`. So
   "restrict along the augmentation", "reduce mod `q`", "read over the base" are all one
   `Spec.map_comp`. **Every base morphism in this development is `Spec.map` of a local hom**
   (`SpecLoc.special toF`, `specFDStr`, `specFDAug`), so this applies to all of them.
3. **The structure morphism becomes a ring map by `Spec.map_surjective`**: `fromSpecStalk p ≫ xstr`
   is `Spec.map β` for a unique `β : R ⟶ 𝒪_{X,p}`, and then "being a section" is literally
   `β ≫ ψ = 𝟙`. That is the step that lets a tangent vector be checked to lie over the base
   by a one-line computation instead of a chart argument.

**`rw` WILL FAIL ON A TERM IT PRINTS IDENTICALLY — MAKE THE MORPHISM OPAQUE.** Building the
tangent vector as `CommRingCat.ofHom (ofDeriv f d h1 hmul)` and then `rw`-ing with a lemma
about that same expression fails with *"Did not find an occurrence of the pattern"* followed
by the pattern and a target that contain it character for character. Two causes, both real
here: `CommRingCat.ofHom` produces a morphism between `CommRingCat.of ↥X` rather than `↥X`
(so `CommRingCat.hom_ofHom` cannot match), and `CommRingCat.Hom.hom` vs the structure field
`hom'` print the same. **The cure is one `obtain`:**

    obtain ⟨τ, hτloc, hτfst, hτsnd⟩ :
        ∃ t : 𝒪 ⟶ CommRingCat.of (DualNumber k), IsLocalHom t.hom ∧
          (∀ a, TrivSqZeroExt.fst (t.hom a) = f a) ∧ (∀ a, TrivSqZeroExt.snd (t.hom a) = d a) :=
      ⟨CommRingCat.ofHom (ofDeriv f d h1 hm), …⟩

`τ` is then a free variable with only its characterising equations, every later `rw` matches,
and the construction is never unfolded again. This is the same lesson CLAUDE.md already records
as *"`let`-binding a structure literal is the expensive way to name a map; `obtain`-ing it from
an `∃` is the cheap one"* — note it applies to `set` too, which caused exactly these failures
before being removed.

### The mathematical half: an audit's "this hypothesis is consumed TWICE and cannot be dropped" is a claim about ITS route

That leaf's audit routed through completions — dualise tangent injectivity to cotangent
surjectivity, Nakayama on `𝒪̂`, compare on the residue disc — and correctly observed that
this spends `Smooth xstr` twice (finite-dimensionality of the cotangent space, and
noetherianity of the stalk) and needs `𝒪_{AZ,ā}` noetherian too, which is what the
abelian-scheme hypothesis was buying. It called that second one "the honest wart".

**The `q`-adic induction needs neither, so both hypotheses are unused.** Assume
`φ ≡ ψ (mod qⁿ)` and set `D := (φ − ψ)/qⁿ`; the Leibniz identity
`φa·φb − ψa·ψb = φa(φb − ψb) + (φa − ψa)ψb` is EXACT in the base ring, so `D` is a genuine
`ψ`-derivation with no truncation, hence an `𝔽_q[ε]`-point; tangent injectivity kills it
against the zero derivation; `⋂ₙ qⁿ = 0` finishes. No completion, no Nakayama, no duality —
therefore no noetherian hypothesis anywhere.

Two things to carry:

* **When an audit says a hypothesis is load-bearing, check whether it is load-bearing for the
  STATEMENT or only for the route.** Here it was the route, and the tell was that the audit
  named the SAME hypothesis for two different technical purposes (finite-dimensionality and
  noetherianity) — both of which are artefacts of passing to completions.
* **Keep the signature anyway.** Deleting `_hsm`/`_abZ` is a signature change with call sites
  in a file other agents are editing; an unused hypothesis costs the prover nothing. Say in
  the docstring that they are unused and name the sharper statement — that is a decision the
  next owner can act on, and it is the cheap side of the interface-split hazard.

### Derive the base's arithmetic from the AXIOMS, not from the neighbouring file's API

`IsReductionBase q R toF` has exactly two clauses (`toF` surjective; `ker toF = nonunits`).
X0.lean has grown a large API over them, but that API is *in X0.lean*, and importing an
80 000-line module into a mathlib-facing helper to reach four short lemmas is the wrong trade.
Re-deriving them from the two clauses is ~120 lines and buys a module with **no project
dependency at all**, which `X1.lean` can reuse. Worth knowing what falls out for free:

* `R` local, `toF` local, `ZMod q` local (`IsLocalRing.of_surjective'` along `toF`);
* `q ≠ 0` (at `q = 0` the residue ring is `ℤ`, where `2` is neither zero nor a unit);
* **`q` PRIME** — not in X0.lean's API, and it is 15 lines: every non-zero element of `ZMod q`
  is a unit, which `ZMod.isUnit_iff_coprime` refutes at a proper divisor of a composite `q`;
* `𝔪_R = qR` and `R ⊆ ℤ_(q)`, both from ONE primitive: `1/den ∈ R` for every `r ∈ R`, by
  Bézout on `num`/`den` (`u·num + v·den = 1` gives `1/den = u·r + v`). That single fact
  replaces X0.lean's `not_dvd_den`, `isUnit_den` and `mem_of_not_dvd_den`;
* `q`-adic separatedness, via `padicValRat` once `Fact q.Prime` is available.
