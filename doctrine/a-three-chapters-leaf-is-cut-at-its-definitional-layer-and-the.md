## A "THREE CHAPTERS" LEAF IS CUT AT ITS DEFINITIONAL LAYER — AND THE LAYER IS CHEAP IF YOU STATE IT ON TEST SCHEMES
(2026-08-01, `flt-lean-350`, `exists_groupSchemeModel_of_weakNeronModelData` — BLR
*Néron Models* §§4.2–4.3, 5, 6.) Some leaves are priced at whole chapters and the
price is right. What is usually WRONG is the assumption that the cut needs the
whole vocabulary of those chapters. Here the interface between the two halves is
"an `S`-birational group law" (BLR 5.1/1), and the reflex is to build BLR §2.5
first — `S`-rational maps as equivalence classes, domains of definition, graphs,
schematic images. **None of that is needed to STATE the cut**, and skipping it took
the definitional layer from a module to ~180 lines that compile in 6 s.
Three moves did it, and each is reusable wherever a partial/rational structure has
to appear in a statement:
* **Carry the partial morphism as DATA, not as a class.** A group law needs exactly
  ONE partial morphism, so the pair `(domain : X.Opens, mul : ↑domain ⟶ X)` is the
  whole of it. Equivalence classes are needed only where a statement quantifies over
  *all* representatives — which, for a structure you are PRODUCING in one leaf and
  CONSUMING in the next, it never does.
* **State fibrewise density TOPOLOGICALLY.** BLR's `S`-dense ("`U_s` is dense in
  `X_s` for every `s`") is `∀ s, f.base ⁻¹' {s} ⊆ closure (A ∩ f.base ⁻¹' {s})` —
  no `X ×_S Spec κ(s)`, no residue fields. Two remarks make it BLR's condition on
  the nose and both belong in the docstring: closure-in-`X` met with the fibre IS
  closure in the fibre's subspace topology, and `X ×_S Spec κ(s) ⟶ X` is a
  homeomorphism onto the set-theoretic fibre.
* **State associativity ON TEST SCHEMES.** "`(xy)z = x(yz)` wherever both sides are
  defined" reads as needing `X ×_S X ×_S X` and an `S`-dense open of it. It does
  not: quantify over `a b c d : T ⟶ ↑domain` with five equations saying `a = (x,y)`,
  `b = (y,z)`, `c = (xy,z)`, `d = (x,yz)`, and conclude `c ≫ mul = d ≫ mul`. A test
  point of `domain` IS a pair of points landing in the domain, so this quantifies
  over exactly the situations where both sides are defined — and it is the
  functor-of-points idiom the surrounding file is already written in.
**And take the SHRUNK representative.** BLR ask that the universal translations `Φ`,
`Ψ` be `S`-birational (∃ an `S`-dense open on which each is an open immersion onto
an `S`-dense open); asking instead that they be open immersions **on `domain`
itself** removes an existential from every clause and is equivalent up to the choice
of representative — BLR's own remark after 5.1/1 gives one direction, and shrinking
to the intersection gives the other, associativity surviving because it is a
statement about test points that land in the domain. **Write that translation
paragraph into the structure's docstring**: without it the definition looks like a
strengthening a producer might not be able to meet.
### WHERE TO PUT THE CLAUSE THAT BELONGS TO NEITHER HALF
The interesting design question was not the two halves but the third thing: *the
solution of the birational group law still extends étale points* (BLR's translation
argument, 4.4/4). It is Néron-flavoured, so putting it on the general half would
destroy the only reason to isolate that half. **Put such a clause on the
DOMAIN-SPECIFIC leaf, quantified over the output of the general one** —
`∀ G, ∀ solution structure on G, <clause>` — and then the glue is three lines:
apply leaf A, apply leaf B, feed B's output to A's clause.
**A clause of that shape is a `∀` over a structure, so it owes the junk-witness
audit, and the audit is not automatic.** Two things had to be checked here and both
are cheap: the solution is pinned by BLR 5.1/3 (uniqueness up to canonical
isomorphism), so `∀ solution` and `∃ solution` agree; and the clause also quantifies
over an `IsFibreIdent`, which is NOT pinned — two of them differ by an automorphism
`α` of the generic fibre — so one has to check the clause is invariant under `α`. It
is, because the clause reads `∀ u, ∃ uZ, u ≫ gen.universalPoint = …` and `u ↦ u ≫ α`
is a bijection of the quantified set. **Write the invariance argument down**; it is
what licenses omitting a compatibility hypothesis that would otherwise have to be
produced by the other leaf and threaded through the glue.
### THE COUNT GOES UP, AND THE THING TO REPORT IS WHAT LEFT THE LEAVES
`1 → 2`, and no mathematics was done. What changed: neither residue is three
chapters; the second names no object of the file's vocabulary (no `ω`, no weak Néron
model, no extension property) and is stated as the theorem Weil, Néron and Artin
proved; and the shared citation both residues spend — Weil's extension theorem
4.4/1, which the sibling leaf downstream spends a THIRD time — is now named in three
docstrings as the next cut. **A citation that three leaves spend is worth more than
a leaf: say so where each of the three will be read**, since nothing else links them.
