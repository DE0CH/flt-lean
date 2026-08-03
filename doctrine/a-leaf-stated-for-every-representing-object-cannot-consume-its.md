## A LEAF STATED FOR *EVERY* REPRESENTING OBJECT CANNOT CONSUME ITS OWN CITATION

(2026-07-31, `RelativePicard.lean`, and this closed two leaves and created none.)

This development states representability through structures — `IsRelPicOf strX pstr`,
`IsJacobianOf`, `IsAlbaneseOf`, `AbelianSchemeStruct`, `IsRelPicZeroOf` — and then states
properties of the represented object in the shape

    (hP : IsRelPicOf strX pstr) : Smooth pstr

i.e. **EVERY scheme representing the functor has the property**. That shape is *true* (Yoneda pins
the object up to isomorphism) and is what a consumer wants, but **it is not what any textbook
proves.** BLR does not show "every scheme representing `Pic_{X/S}` is smooth"; it CONSTRUCTS one —
inside a Quot/Hilbert scheme, separated and locally of finite type by construction — and reads
smoothness off the construction. So a prover dispatched at the "every" form has no citation to
follow at all: they must first invent the missing bridge, and the leaf reads as research-scale when
the mathematics under it is a page of BLR.

**The bridge is one PROVABLE lemma, and it is pure Yoneda on the points type.** Given two
structures `hP : IsRelPicOf strX pstr` and `hQ : IsRelPicOf strX qstr`:

* `cmp` sends a `T`-point of `P` to the point of `Q` with the same class — `surj` for existence,
  `inj` for uniqueness;
* `cmp_cmp` (round trip) is `inj` again;
* `cmp_pre` (naturality in the test object) is the ONLY step with content — chain the two
  `sheaf_pre` fields with the transport lemma for the equivalence relation;
* `toHom := (cmp (tautological point 𝟙 P)).1`, and `toHom_comp_toHom` is `cmp_pre` at
  `h = toHom` composed with `cmp_cmp`. That gives `P ≅ Q` over `S`.

Roughly 60 lines, no geometry, and it compiled first try. Then **any isomorphism-invariant property
transports**: `rw [← toHom_comp]; infer_instance` proves `Smooth pstr` from `Smooth qstr`, because
an iso is an open immersion and both `Smooth` and `IsSeparated` are stable under composition.

**Then move the property into the EXISTENCE leaf, not into a new leaf.** With the bridge, "every"
reduces to "SOME representing object has it", and that existential is threaded up the chain of
existence theorems to the one leaf where a scheme is actually constructed
(`exists_relPicOf_isAffineOpen`). The clause is absorbed by an EXISTING sorry; no leaf is created.
Here the frontier went **9 → 7** while the total mathematical obligation was unchanged — the two
"every"-shaped leaves disappeared and FGA 232's owner gained a clause they were always going to
have in hand.

**The generalisable test, worth running before attacking any leaf of this shape:** ask whether the
citation named in the docstring proves a statement about *all* objects of a class or about *one
constructed* object. If it is the latter and the leaf says the former, **stop and prove the
uniqueness lemma first** — the leaf is not hard, it is mis-shaped. Symptom to watch for: a leaf
whose only hypothesis with content is a representability structure, and whose conclusion is a
property of a scheme that the structure says nothing about topologically.

Two smaller notes from the same task. **Threading a clause into an existence leaf's conclusion is a
RESTATEMENT**, so every earlier faithfulness audit on that leaf is VOID and must be re-run against
the composite — the strengthened hypothesis and the strengthened conclusion of a gluing leaf move
in *opposite* directions, which is precisely the shape CLAUDE.md already records as able to be
fatal. And the reduction may need a hypothesis the leaf did not have: `smooth_of_isRelPicOf` gained
`o : RelPoint strX (𝟙 S)` because the existence theorem needs a section. Adding a hypothesis
WEAKENS a leaf and is safe **only after checking the consumer can supply it** — here
`exists_relPicZeroOf_of_relPicGroupLaw` already had `o` in scope, so the change cost one argument
at one call site.

