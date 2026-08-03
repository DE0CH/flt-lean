## AN AUDIT'S COUNTEREXAMPLE MUST BE CHECKED AGAINST THE HYPOTHESIS IT REFUTES — and a "monicity is local" route is usually the expensive one

(2026-07-31, `flt-lean-248`, closing `mono_modTensorToUnit` in
`ModularCurve/RelativePicard.lean`.)  That leaf carried a FAITHFULNESS AUDIT headed
**"every hypothesis is load-bearing"** with a witness for each.  Two of its four
hypotheses are not used at all, and the witness offered against dropping `[IsIntegral X]`
**does not satisfy the hypotheses it is offered against** — and it says so itself, in the
same sentence:

> Drop integrality: over `X = Spec k[x,y]/(xy)` take `I = (x)`, `J = (y)`.  **Both are
> invertible on the two components separately**, `I ⊗ J` is nonzero, and the product map
> is zero, so it is not monic.

"Invertible on the two components separately" is the concession that `(x)` is NOT
invertible on `X`: `Ann_R(x) = (y)`, so `(x) ≅ R/(y) ≅ k[x]`, which at the origin is a
module killed by a nonzero element of the local ring and so is not free of rank one
there.  The hypothesis fails at exactly the point where the conclusion does.  So the leaf
is TRUE without integrality, and the proof below never mentions it.

**The check is one line per witness and nobody runs it: instantiate the witness and
verify EVERY SURVIVING hypothesis on it, not just the one being dropped.**  A
counterexample licenses precisely one claim — that the statement with that hypothesis
removed is false — and it licenses nothing at all if it is not an instance of the
remaining hypotheses.  This is the same family as the already-recorded
"a counterexample is only as strong as the hypothesis list it was tested against", with
the failure one step earlier: there the witness was real and over-attributed, here the
witness is not a witness.  **The tell is a hedge inside the witness** — "on the two
components separately", "after normalisation", "generically" — which is where the author
noticed the gap and wrote past it.

### The route: `ModLM`, and why "monicity is local" is the expensive way

The leaf's recorded route was LOCAL — trivialize `I` and `J` on a common `U`, read
`I ⊗ J ⟶ 𝒪` as multiplication by `ab ∈ Γ(X, U)`, and use that an integral scheme has
domains for section rings.  That needs three things this pin does not have: monicity of a
map of `𝒪`-modules being local, a compatibility of `modTensor` with restriction, and the
domain theory.  Estimated at ~1000 lines.

**The formal route is ~150 lines and needs none of it**, because this file already built
`ModLM Z` — `Z.Modules` carrying the LOCALIZED MONOIDAL STRUCTURE, a genuine
`MonoidalCategory` with a natural associator and unitors, put there for the associator
`nonempty_modTensor_assoc`.  In it:

* `f ⊗ₘ g = (f ▷ M) ≫ (𝒪 ◁ g)` (`tensorHom_def`);
* **tensoring by an INVERTIBLE object is an equivalence, hence preserves monos** — from
  `M ⊗ N ≅ 𝟙_`, the family `(X ⊗ M) ⊗ N ≅ X` (associator, then `X ◁ e`, then the right
  unitor) is a two-sided pointwise inverse of `- ▷ M`, and its naturality is three
  rewrites (`associator_naturality_left`, `whisker_exchange`, `rightUnitor_naturality`);
* `𝒪 ◁ g` is conjugate to `g` by the LEFT UNITOR, which is natural.

So only ONE of the two sheaves need be invertible.  The bridge back is
`Functor.Monoidal.map_tensor` applied to the sheafification-as-monoidal-functor, plus
naturality of the sheafification adjunction's COUNIT — `modTensorMap f g` is
`(modLocA X).map (f.val ⊗ₘ g.val)` **by `rfl`**, which is the fact that makes the whole
thing cheap and which one `example ... := rfl` in a scratch settles in four seconds.

**Generalisable: when a statement about `modTensor` is priced at a local argument, ask
whether it is a formal consequence of the monoidal structure `ModLM` already carries.**
Every audit in that file lists "no associator, no unitor" as the standing obstruction;
that has been false since 2026-07-28 and the file says so 6000 lines above the leaf.

### Two Lean traps that cost four of the six iterations, both about DEFEQ-BUT-NOT-SYNTACTIC

* **State a natural isomorphism POINTWISE, not as `F ⋙ G ≅ 𝟭 C`.**  The components of
  the latter have type `(F ⋙ G).obj X ⟶ (𝟭 C).obj X`; `(𝟭 C).obj X` is `rfl`-equal to
  `X` and NOT syntactically equal to it, so `rw [φ.hom.naturality u]` fails on a goal
  that prints correctly, and `Mono (φ.hom.app A ≫ u)` **fails to synthesize** although
  `Mono u` is in context.  Taking `(φ : ∀ X, G.obj (F.obj X) ≅ X)` plus its naturality
  EQUATION as separate arguments makes every one of those steps go through unchanged.
  Same family as the standing `(𝟭 _).obj` note, met in the reverse direction: there it
  broke `rw`, here it also breaks INSTANCE SEARCH, which is silent about why.
* **Across a TYPE SYNONYM, pass a factorisation equation as an EXPLICIT argument, never
  as an instance.**  `ModLM X` is a type synonym for `X.Modules` with
  `inferInstanceAs (Category _)`, so a `⊗ₘ` elaborated in a lemma's statement and a
  `⊗ₘ` elaborated at the call site can pick the monoidal instance up by different routes
  and be defeq but not syntactically equal.  Instance search cannot cross that;
  an explicit argument is checked up to defeq and can.  Concretely: `mono_of_mono_fac w`
  searching for `Mono <RHS of w>` failed against a hypothesis that was literally in
  context, and wrapping it as a lemma taking `w` explicitly fixed it.  The generic
  symptom is "failed to synthesize `Mono X`" where `X` prints identically to something
  you are holding.

