## A STRUCTURE WHOSE AXIOMS ARE ALL EQUATIONS BETWEEN MORPHISMS IS PROBABLY SATISFIED BY THE IDENTITY — and its leaf's own NON-VACUITY paragraph is where the refutation is hiding
(2026-08-02, `flt-lean-322`, `Modularity/MoretBailly.lean`.)  A cut that puts a
`structure` between two leaves is the standard move here, and it has a failure
mode that no falsity audit of either leaf can see, because the defect is in
neither statement: **the structure is satisfied by the trivial assignment, so the
leaf that RECEIVES it receives nothing.**
`SplitModuliLevelAction` (Taylor's level-changing action of `SL₂ × SL₂` on
`X₀ ⊗ ℚ̄`) has five fields: `act`, and four EQUATIONS — `act g gp ≫ snd = snd`,
`act 1 1 = 𝟙`, `act (g₁g₂) (gp₁gp₂) = act g₁ gp₁ ≫ act g₂ gp₂`, and a
`baseAct`-conjugation clause.  Every one of them holds for `act g gp := 𝟙`, with
no hypotheses at all:
    act _ _ := 𝟙 _
    act_snd _ _ := Category.id_comp _
    act_one := rfl
    act_mul _ _ _ _ := (Category.id_comp _).symm
    act_baseAct _ _ _ _ _ _ _ := by simp
Six lines, and they settle the question.  Two consequences followed at once: the
sibling leaf asking for `Nonempty (SplitModuliLevelAction …)` was **TRIVIALLY
TRUE** (closing it would have moved the frontier count and nothing else — a
phantom waiting for a dispatch), and the consumer leaf's `act` hypothesis was
decoration.
**THE CHECK IS SIX LINES AND BELONGS ON EVERY STRUCTURE YOU CUT THROUGH: write
the trivial/identity/zero inhabitant and see whether it compiles.**  A structure
whose fields are all equations between morphisms — an action, a descent datum, a
compatibility package, a "the diagram commutes" bundle — is the high-risk shape,
because identities satisfy equations.  What rules the trivial witness out is
always a field that CONSTRAINS THE VALUE (here: what the action does to the
universal family, or to the level structure), and that is exactly the field such
cuts omit, because it is the one that needs the objects the interface was
introduced to avoid mentioning.
**AND THE REFUTATION IS USUALLY ALREADY WRITTEN, IN THE LEAF'S OWN NON-VACUITY
PARAGRAPH, WITH THE SIGN REVERSED.**  That leaf carried, in bold:
> THE `∀`-OVER-TWISTS SHAPE IS NOT VACUOUS … `isGaloisTwistForm_one` makes `X₀`
> its own twist by the trivial cocycle, so at `c = 𝟙` the statement would assert
> `ρbar`-equivariant level structures on `X₀` itself, which is false whenever
> `ρbar ≇ ρ₀`.  So the clause carries the whole "descend along the twist"
> content and cannot be discharged trivially.
Every clause is true.  The inference is backwards, and the tell is that the
paragraph never asks whether `c = 𝟙` is REACHABLE inside the leaf's hypotheses.
It was — via the trivial action — so the sentence does not show the clause
carries content; it shows the hypotheses do not determine the object.  **Read
every "this is not vacuous, because at the degenerate value the conclusion would
be false" paragraph as a conditional refutation, and then go and decide the
antecedent.**  If the degenerate value is reachable, you have a THIRD-OUTCOME
leaf (neither provable nor refutable) and the paragraph is its audit.
**THE REPAIR IS THE ONE THIS FILE ALREADY PRESCRIBES, AND HERE IT LOWERS THE
COUNT: make the leaf PRODUCE the datum instead of receiving it.**  `∃ act, ∀ X,
IsGaloisTwistForm … (act.twistCocycle …) → <old conclusion>` fuses the producer
leaf and the consumer leaf into one, and the `∀`-over-twists clause then FORBIDS
the trivial action instead of being undermined by it.  Two open leaves became
one.  Three things made it cheap, and they are what to check before choosing
fusion over "strengthen the structure":
* **the two leaves had ONE consumer between them, and it obtained both from the
  same place** — so the rewiring was `obtain ⟨act, hact⟩` plus one application,
  and no signature outside the pair moved;
* **strengthening the structure instead would have meant inventing an interface**
  (here: the base-changed universal family and an isomorphism `(act g gp)^* A₀K ≅
  A₀K` compatible with the group law and the `𝒪_D`-action) with no producer to
  test it against.  Fusion needs no new vocabulary;
* **keep the vacuity witness in the file as a PROVEN theorem, not in the report.**
  `∃ act : Structure …, ∀ σ, act.twistCocycle … σ = 𝟙 _` is one declaration whose
  statement IS the finding, it consumes the trivial inhabitant so nothing floats,
  and it is what stops the next agent re-cutting the same interface.
Related but distinct from the recorded **AN INTERFACE PREDICATE CAN BE
UNDER-COMMITTED** (satisfied by the wrong NORMALISATION — a scaling family of
wrong witnesses) and from **THE DEGENERATE OBJECT REFUTES EVERY UNGUARDED
PERFECTNESS CLAUSE** (the degenerate OBJECT).  Here the object is fine and the
degenerate thing is the MORPHISM DATA, which is the case a `structure` between
two leaves manufactures.
