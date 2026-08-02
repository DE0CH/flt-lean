---
name: flt-structure-of-equations-is-satisfied-by-identity
description: "A cut-through structure whose fields are all equations between morphisms is usually satisfied by the identity, so the leaf receiving it receives nothing — and its own non-vacuity paragraph is the refutation with the sign reversed."
metadata: 
  node_type: memory
  type: project
  originSessionId: 524243e6-b721-4c12-9534-e97afa55ff3b
  modified: 2026-08-02T18:33:46.967Z
---

(2026-08-02, `flt-lean-322`, `Modularity/MoretBailly.lean`, `SplitModuliLevelAction`.)
When a cut puts a `structure` between a producer leaf and a consumer leaf, write the
TRIVIAL inhabitant and try to compile it. If every field is an EQUATION between
morphisms — `act g gp ≫ snd = snd`, `act 1 1 = 𝟙`, multiplicativity, a conjugation
clause — the identity satisfies all of them, with no hypotheses, in about six lines
(`Category.id_comp`, `rfl`, `(Category.id_comp _).symm`, `by simp`). Then the producer
leaf is TRIVIALLY TRUE (a phantom waiting for a dispatch) and the consumer's hypothesis
is decoration: neither provable nor refutable, i.e. [[flt-third-outcome-strengthen-the-axioms]].

What rules the trivial witness out is always a field CONSTRAINING THE VALUE (what the
action does to the universal family / the level structure), and that is exactly the
field such a cut omits, because it needs the objects the interface was introduced to
avoid naming.

**The refutation is usually already written, in the leaf's own NON-VACUITY paragraph,
with the sign reversed.** "At the degenerate value `c = 𝟙` the conclusion would be
false, so the clause carries content" is a CONDITIONAL refutation; the paragraph never
asks whether `c = 𝟙` is REACHABLE inside the hypotheses. If it is, the hypotheses do
not pin the object. Same family as [[flt-ask-what-the-countermodel-fails]].

**How to apply:** repair by making the leaf PRODUCE the datum — fuse the producer and
consumer into `∃ act, ∀ X, …(act)… → <old conclusion>`, so the `∀` clause forbids the
trivial witness instead of being undermined by it. Here that took 2 open leaves to 1
with no signature outside the pair changing, because the two leaves had ONE consumer
between them and it obtained both from the same place. Prefer fusion to strengthening
the structure when strengthening would mean inventing an interface with no producer to
test it against. Keep the vacuity witness in the file as a PROVEN theorem whose
statement IS the finding (`∃ act : S …, ∀ σ, act.twistCocycle … σ = 𝟙 _`), so it
consumes the trivial inhabitant and nothing floats.

Distinct from [[leaf-falsity-can-live-in-a-definition]] (wrong normalisation inhabits
the predicate) and from the degenerate-OBJECT trap: here the object is fine and the
degenerate thing is the MORPHISM DATA.
