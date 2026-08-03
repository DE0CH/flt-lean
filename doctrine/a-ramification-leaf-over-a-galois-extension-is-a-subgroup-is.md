## A RAMIFICATION LEAF OVER A GALOIS EXTENSION IS A SUBGROUP-IS-TRIVIAL LEAF — the pin has the dictionary on BOTH sides
(2026-07-31, `flt-lean-38`, `NumberField/UnramifiedClassFieldExistence.lean`.)
Two sibling leaves — *the compositum of two everywhere-unramified extensions is
unramified*, once at the FINITE primes and once at the INFINITE places — were cut with a
docstring saying all three clauses of their parent "were ALL THE SAME ARGUMENT" over the
shared engine `forall_mem_sup_of_fixed`. That claim was right and it is only half of why
they are cheap. **The other half is that mathlib turns each ramification statement into a
statement that a SUBGROUP OF `Gal(M/K)` IS TRIVIAL, and it has that dictionary on both
sides of the archimedean/nonarchimedean divide:**
* archimedean — `NumberField.InfinitePlace.isUnramified_iff_stabilizer_eq_bot [IsGalois k K] :
  IsUnramified k w ↔ MulAction.stabilizer Gal(K/k) w = ⊥`;
* nonarchimedean — `Ideal.card_inertia_eq_ramificationIdxIn` (`#(Q.inertia G) = e_in`) plus
  `Ideal.ramificationIdxIn_eq_ramificationIdx` plus `Ideal.ramificationIdx_eq_one_iff`
  (`e = 1 ↔ Algebra.IsUnramifiedAt`).
So a leaf whose conclusion is *"this prime/place is unramified"* over a Galois extension
should be re-read as *"this subgroup is trivial"* BEFORE it is priced. Each of these two
was ~40 lines. **And the two instance obligations that look like they will cost a
development are found by SEARCH at this pin** — `IsGaloisGroup Gal(L/K) (𝓞 K) (𝓞 L)`
(through `IsGaloisGroup.of_isFractionRing`) and `PerfectField (Q.under (𝓞 K)).ResidueField`
— which is the single fact that decides the cost. Probe them with a two-line
`example … := by infer_instance` in a scratch before writing anything; it takes five
seconds and it is the whole feasibility study.
**THE DICTIONARY IS CHEAP, NOT OPTIMAL, AND ON THE ARCHIMEDEAN SIDE IT IS NOT THE BEST
ROUTE.** The stabiliser proof of the archimedean clause needs `[IsGalois K Lᵢ]`; `merger`
had meanwhile proven the same leaf by an EMBEDDING argument — extend `w.embedding` to
`AlgebraicClosure K`, show `conj ∘ Φ = Φ` on each `Lᵢ`, conclude on the sup with
`NumberField.eqOn_sup_of_eqOn` — which needs no Galois hypothesis at all and is therefore
strictly stronger. So the dictionary is the right thing to reach for FIRST, and once the
leaf is closed it is worth asking whether the hypotheses it forced are really necessary:
here the finite-prime clause's `[IsGalois]` is an artefact of the route (the general
statement is true, `K_𝔭^{ur}` being a field) and the archimedean one's was avoidable
outright.
**The docstrings' own "route not to try" was right and its reason was wrong.** They
forbade `Algebra.FormallyUnramified.baseChange` on `𝓞 L₁ ⊗ 𝓞 L₂` because the conductor of
`𝓞 L₁ · 𝓞 L₂` in `𝓞 (L₁L₂)` need not be the unit ideal. True globally; LOCALLY at an
unramified prime it *is* the unit ideal, and the route dies for a different reason — it
needs "étale over a normal domain is normal", which this pin does not have. Correct the
reason as well as keeping the verdict: a wrong reason attracts repairs that cannot work.
### A LEAF'S RECORDED ROUTE CAN PRESUPPOSE A HYPOTHESIS THE STATEMENT DOES NOT CARRY
Both leaves were stated over ARBITRARY finite subextensions, and both of their recorded
routes restrict an element of `Gal(K̄/K)` to `Lᵢ` — which needs `Normal K Lᵢ`. So the
statements were strictly more general than the arguments written on them, and nobody had
noticed because the two are separated by a screen of prose.
**When that happens and the CONSUMER already supplies the missing hypothesis, add it.**
Adding a hypothesis is a weakening, so the leaf's faithfulness audit transfers verbatim and
the refutation check it names is unaffected. Two things make it cost nothing here and both
must be CHECKED rather than assumed:
* **the added hypotheses were INSTANCE-IMPLICIT**, and the consumer's `IsAbelianGalois K Lᵢ`
  extends `IsGalois K Lᵢ`, so instance search supplies them and **not one character of the
  call site moved**. That is the difference between a signature change that is a class-7
  merge hazard and one that is invisible; verify it with the build, not by reading;
* **the general statement's status must be settled and written down.** For the finite-prime
  clause the non-Galois statement is TRUE (classically because `K_𝔭^{ur}` is a FIELD) and a
  completion-free route exists — normal closure, `Ideal.ramificationIdx_tower`,
  `card_inertia_eq_ramificationIdxIn` over the two bases `𝓞 K` and `𝓞 Lᵢ`, transported onto
  `Lᵢ.fixingSubgroup` by `IntermediateField.fixingSubgroupEquiv` and `Ideal.inertiaEquiv` —
  so the docstring says so and says to STRENGTHEN in place rather than add a rival
  declaration. For the archimedean clause the hypothesis is closer to essential. Those are
  different answers and a reader must not have to guess which.
**Corollary about ordering: close the SIBLING in the same run.** The second leaf cost about
a quarter of the first, because the engine, the instance setup and the restriction lemma
were already in hand — the only new input was one mathlib `iff`. A cut whose docstring says
two leaves are the same argument is telling you to budget them together, and the saving is
lost if the second is dispatched a release later.
### … AND RUN THE `merger` CHECK ON THE SIBLING TOO — the rule is per DECLARATION, not per TASK
The sibling above had to be **thrown away**: `merger` already proved it, better. I ran
`git show merger:<file> | grep -n <name>` for my assigned TARGET — correctly, and it was
still `sorry` there, so that proof stands — and did not re-run it for the leaf I decided to
close forty minutes later. One command, skipped once, and a complete verified proof went in
the bin.
**So: the release-window check is keyed on the DECLARATION you are about to write, not on
the task you were given.** Any leaf you decide to attack mid-run — a sibling, a helper you
notice is open, a residue of your own cut — needs its own `git show merger:` before the
first line of it is written. And the cheapest second net is the QUEUE: `~/.flt-loop/queue2`
is a 2.4 MB text file, and one `grep` of it for your leaf's name would have caught this in
seconds, because a task had already been queued to *generalise* the leaf, which only makes
sense if it is proven. Grep the queue for every declaration you intend to touch:
    grep -c '<declName>' ~/.flt-loop/queue2      # a task about it ⇒ read that task
**When it fires, DECLINE your own payload — and revert it to make the merge a NO-OP, not a
conflict.** Restore the region byte-identically to your base (here: `git checkout <my first
commit> -- <file>`, then re-apply only the parts that are still wanted), delete anything
that becomes consumerless in the process, and name your own commit sha in the message so
the discarded proof stays recoverable. `git merge-tree --write-tree --name-only HEAD merger`
then reports the file as *Auto-merging* with no conflict, which is the receipt that the
decline is complete — run it before and after; before, it named the file as CONFLICT.
### Three mechanical notes from the same run
* **`ArtinSymbol.lean`'s `algebraMap_restrictNormalHom_smul` does NOT cover a compositum.**
  It is stated for an intermediate field of a fixed ambient NUMBER field; `L₁ ⊔ L₂` is an
  intermediate field of `AlgebraicClosure K`, and the tower `Lᵢ ⊆ L₁ ⊔ L₂` has to be built
  by hand from `IntermediateField.inclusion`. The replacement
  (`algebraMap ↥E ↥F (restrictNormalHom E ρ x) = restrictNormalHom F ρ (algebraMap ↥E ↥F x)`)
  is `AlgEquiv.restrictNormal_commutes` twice, compared inside `AlgebraicClosure K`, and its
  RING-OF-INTEGERS and INFINITE-PLACE corollaries are three lines each. Pass the coercion
  compatibility `∀ x, (algebraMap ↥E ↥F x : K̄) = (x : K̄)` as an EXPLICIT argument — it is
  `rfl` at every call site, whereas the `IsScalarTower` route builds an instance only to
  unfold it again.
* **A near-duplicate one module DOWNSTREAM can force your NAME.**
  `HilbertClassFieldNormal.lean` (which transitively imports the file being edited) already
  carried both halves of the inertia dictionary, at the `AlgebraicClosure ℚ` specialisation,
  as `eq_one_of_mem_inertia_of_unramifiedAt` and `isUnramifiedAt_of_inertia_trivial`. The
  upstream general versions cannot take the second of those names — one namespace, two
  declarations, and the module that imports both stops compiling. Grep the whole tree for
  the name you are about to use, not just your own file; and when the downstream copy is an
  INSTANCE of what you just proved, say so in its docstring and queue the deletion rather
  than doing a cross-file edit you were not sent at.
* **To move such a relation onto `InfinitePlace`, apply it at `ρ⁻¹`, not at `x` transported
  by `.symm`.** `InfinitePlace.smul_eq_comap` is `σ • w = w.comap σ.symm`, so the two sides
  differ by the INVERSE automorphism; `map_inv` for the monoid hom
  `AlgEquiv.restrictNormalHom` supplies it, and feeding the lemma `ρ⁻¹` at the ORIGINAL
  point is what makes `simpa [map_inv]` close it. Feeding it `τ.symm x` produces a double
  `.symm` and a type mismatch that looks like a real error.
* **`NumberField.InfinitePlace.isUnramified` takes the BASE field explicitly** —
  `InfinitePlace.isUnramified K w`, not `InfinitePlace.isUnramified w`. The error is an
  "Application type mismatch" showing `∀ (w : InfinitePlace ?m), IsUnramified ?m w`, which
  reads as a unification failure and is a missing argument.
