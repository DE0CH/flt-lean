---
name: flt-cut-a-chapter-leaf-by-assembly
description: "A chapter-scale leaf is cut by REWRITING ITS BODY as an assembly over new leaves; a new definition parked beside an untouched `sorry` is free-floating and gets deleted"
metadata:
  node_type: memory
  type: project
---

When a dispatch says "the realistic deliverable is a DECOMPOSITION", there is
exactly ONE shape that survives this project's free-floating rule, and it is not
the obvious one.

**The obvious and wrong shape**: define the missing object (`PG(X̄,Z)`, a
symmetric power, a Weil restriction), state its existence as a new named leaf
with a good docstring, and leave the target's `sorry` alone. Every declaration
you just wrote is then outside the root cone — *a sorried body contributes no
dependency edges* — so `free-floating.py` reports the lot and the instructions
are "commit and delete". `RelativePicard.lean` even records a one-liner it
refused to keep as a declaration for exactly this reason.

**The shape that works**: turn the target's `sorry` into a real term.

    theorem target ... := by
      obtain ⟨q, hq, hqS⟩ := <PROVEN helper>
      obtain ⟨Z, ι, …⟩     := <new leaf A>
      obtain ⟨P, pstr, ⟨hPG⟩⟩ := <new leaf B, which takes A's output>
      exact <new leaf C> … hPG

Now A, B, C appear in the target's proof TERM, their statements pull in every
definition they mention, and the whole new module is in the cone. The target
stops being a direct sorry; the count goes 1 → 3, which is disclosure.

Two consequences worth planning for BEFORE writing any Lean:

* **Every new definition must appear in the TYPE of some leaf you consume.**
  Lemmas *about* the new object (a group law, an exact sequence, base-change
  compatibilities) are floating unless the assembly itself uses them. Either
  make them `def`s used inside a leaf's statement — `pullbackTrivialisedSheaf`
  is a `def` inside `IsGenRelPicOf`'s naturality field, so it is safe — or do
  not write them yet.
* **Hoist the leaf's NON-geometric existential burdens first; they are free.**
  `exists_skolemBallDatum_of_projectiveCompactification` was asking one leaf to
  produce (i) an auxiliary prime `q ∉ S`, (ii) the boundary `Z` as a scheme, and
  (iii) the whole of Moret–Bailly §3.2–§3.10. (i) is Euclid and is now PROVEN in
  four lines; (ii) is a separate small leaf. Neither had any business inside a
  chapter-scale geometric leaf, and removing them costs nothing and is visible
  progress. Look for this pattern in any `∃ a b c d e, …` leaf: usually at least
  one of the witnesses is cheap and unrelated to the hard part.

The faithfulness cost of the shape: a leaf that receives a NEW object as a
hypothesis is vacuously provable if that object cannot exist. So the leaf
asserting the object's existence must carry its own satisfiability argument in
the docstring (for `Fermat.exists_genRelPic`: rigidification along a faithfully
flat `Z` kills automorphisms, so the naive pair functor is already a sheaf and
`surj` is true as stated — without that hypothesis the leaf would be FALSE).

Related: [[flt-glue-first-no-floating-haves]], [[flt-no-private-shielded-floating]],
[[flt-reduce-to-an-open-leaf-not-a-proof]].
