---
name: flt-universal-binds-base-map-unused
description: "A `universal` field binding `(_g : T ⟶ S)` and never using it is not fine moduli — the fibre-product witness the docstring names fails the ∃!, because the predicate constrains only one projection"
metadata: 
  node_type: memory
  type: project
  originSessionId: 84b9dbfb-c31f-458c-a1cd-e1a7ea6b02b7
  modified: 2026-08-01T14:06:03.907Z
---

`X0.lean`'s representability structures state fine moduli as

    universal : ∀ {T} (_g : T ⟶ S) (e) (L), ∃! m : T ⟶ M, ∃ bc, <pinning>

with `_g` bound and never mentioned — no clause `m ≫ strM = _g`. The file records
that this is a *help* for the assemblies (a rival `m'` need not be an
`S`-morphism) and that is true. It is fatal for the LEAF.

**Why** (2026-08-01, `exists_fullLevelModuliSchemeData_of_isUnit`): the witness the
docstring names is `M = Y(n) ×_{Spec ℤ[1/n]} Spec R`. A morphism `T ⟶ M` is a PAIR
`(t, s)` — the `Spec ℤ[1/n]` compatibility is automatic since `ℤ → ℤ[1/n]` is a ring
epimorphism — and `eM` is pulled back along the FIRST projection, so `∃ bc, <pinning>`
constrains `t` alone. Every `(t, s)` with the right `t` satisfies it, and the `∃!`
fails whenever `Hom(T, Spec R)` has two elements: `n = 3`, `R = ℚ(ζ₃)`, `T = Spec R`,
`s = 𝟙` versus `s = Spec(conjugation)`. `Y(n)` itself DOES satisfy `universal` and has
no `strM : Y(n) ⟶ Spec R`, so the two fields pull opposite ways.

**How to apply:** for any `universal`-shaped field, write down the intended witness and
ask which of its data the predicate constrains. A fibre-product witness whose predicate
mentions one projection has a free other projection. `grep -n '(_g :' <file>` finds every
such binder in seconds. This is invisible to every scan — the statement compiles and the
FALSITY AUDIT is about hypotheses while the defect is in the conclusion's quantifier.

**The contained repair is a hypothesis, not a structure change**:
`hS : ∀ Z, Subsingleton (Z ⟶ Spec (CommRingCat.of R))` (the base is subterminal,
i.e. `ℤ → R` is a ring epimorphism) forces the free component. Adding a hypothesis
cannot make a true leaf false, so the audit transfers verbatim. Putting the clause
`m ≫ strM = g` into the structure instead is canonical but propagates to every
structure in the chain plus everything reading their `universal` — see
[[flt-cut-so-each-half-is-a-consequence]] for why a weaker-from-stronger assembly
breaks. **Measure the threading to its END before pricing it**: here four signatures,
terminating at `nonempty_gamma0AtlasOver_of_isUnit`, which already carried exactly that
hypothesis under exactly that name. Related: [[flt-uniqueness-clause-needs-subsingleton-base]],
[[flt-leaf-hypotheses-are-a-superset]].
