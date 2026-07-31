---
name: lean-op-category-defeq-needs-exact-not-rw
description: "In CommRingCatᵒᵖ diagram work, (D.obj i).unop and (F ⋙ G).obj i never reduce for rw/simp/instance search when D is a def — close those goals with show/exact (full defeq), and give composed diagrams as abbrev plus `show … from inferInstance` instances"
metadata:
  type: reference
---

Building a `Cone`/`IsLimit` over a hand-written diagram `D : I ⥤ CommRingCatᵒᵖ`, every
single failure was the same one, in five costumes:

* `rw [h]` — *"motive is not type correct"* / *"did not find an occurrence"*, because the
  goal carries `↑(Opposite.unop (D.obj n))` where `h` carries `Localization.Away n.val`;
* `simpa … using h` — *"After simplification, term h has type …"*, same mismatch;
* `refine IsLocalization.ringHom_ext M …` — *"failed to synthesize `Algebra A ↑(c.pt.unop)`"*;
* `instance : CompactSpace ((awaySpecDiagram M).obj m)` — not found at the use site even
  though an identical instance was declared, when the diagram is a `def`;
* `congrArg (fun t : _ ⟶ _ => t.unop.hom) h` — *"Invalid field notation"*, the `_ ⟶ _`
  never resolves.

They are all one fact: **`D` is a semireducible `def`, so `D.obj n` is opaque to `rw`,
to `simp`, and to discrimination-tree instance keys — but transparent to `exact`.** The
three moves that work, in order of preference:

1. **`exact` instead of `rw`/`simpa`.** Prove the fact you want as a standalone `have`
   or lemma stated in `Localization.Away n` terms, then `exact` it at the diagram-typed
   goal. Defeq does the rest. This is what turned a stuck `IsLimit.uniq` into one line
   (`exact awayCone_desc_unique s _ h1`) after `simpa only [...]` had failed on exactly
   the same pair of terms.
2. **`show` the WHOLE equation, both sides, before rewriting.** A `show` covering only
   the left factor leaves the right factor diagram-typed and the next `rw` fails anyway.
3. **`abbrev` for a composed diagram** (`D ⋙ Scheme.Spec`), plus instances written
   `show P (Spec (CommRingCat.of …)) from inferInstance`. Then `IsAffine`, `CompactSpace`,
   `QuasiSeparatedSpace`, `IsAffineHom` are all found by `inferInstance` at the use site.

For `congrArg` into the opposite category, name the projections rather than writing a
lambda: `congrArg CommRingCat.Hom.hom (congrArg Quiver.Hom.unop h)` elaborates where
`congrArg (fun t : _ ⟶ _ => t.unop.hom) h` does not.

Related: [[flt-see-the-merge-before-the-merger]] is about merges; this is about a single
file, and it cost roughly a dozen 20-second round trips in a scratch module that
imported only mathlib — which is exactly why the scratch-module rule is worth obeying.
