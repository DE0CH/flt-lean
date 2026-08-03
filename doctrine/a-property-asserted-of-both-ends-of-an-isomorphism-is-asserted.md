## A PROPERTY ASSERTED OF *BOTH ENDS* OF AN ISOMORPHISM IS ASSERTED ONCE — check iso-invariance before calling it load-bearing
(Same run, and it corrects a bullet that had stood since the leaf was cut.)
`exists_constSmul_of_iso` takes `IsInvertibleSubsheaf ιL` **and** `IsInvertibleSubsheaf ιM`
— i.e. invertibility of `L` and of `M` — **and** an isomorphism `e : L ≅ M`. Its audit
claimed *"Drop `IsInvertibleSheaf L` and it is FALSE"*.
It is not false: **`IsInvertibleSheaf` is an isomorphism invariant, so `IsInvertibleSheaf L`
follows from `IsInvertibleSheaf M` together with `e`** — three lines, transport the local
trivialization along `(Scheme.Modules.restrictFunctor U.ι).mapIso e`. The two clauses are
interchangeable and only one of them can be doing anything.
**So add to every faithfulness audit: when a leaf asserts property `P` of two objects that
some hypothesis says are ISOMORPHIC, check whether `P` is iso-invariant.** If it is, at most
one of the two assertions is load-bearing and any counterexample offered against dropping
either is impossible by construction. This is cheap — it is a property of `P`'s definition,
not a search — and it is invisible to the standing "instantiate the witness" discipline,
because there is no witness to instantiate.
**The tell was in the bullet, exactly where CLAUDE.md says to look for it.** The bullet opens
a candidate, writes *"… which is invertible, so instead take …"*, retracts that one too, and
ends without ever exhibiting a witness. A bullet that walks through two or three candidates
and discards each is not a refutation; it is a record of a failed search, and the honest
verdict at the end of such a search is usually "this hypothesis is redundant".
**And the right repair is prose, not signature.** Both clauses were KEPT — a weaker
hypothesis set cannot make a statement false, the sole call site passes all four
positionally, and a signature change is the interface-split merge hazard. What changed is
the audit text. (Same disposition as `mono_modTensorToUnit`'s two unused hypotheses.)
### THE `TopCat.Sheaf` / `Sheaf J` GAP: `rw` fails on a pattern that is character-for-character in the goal
Measured repeatedly in `RelativePicard.lean`, and it cost about half the iterations.
`Z.ringCatSheaf : TopCat.Sheaf RingCat Z` while `SheafOfModules` wants
`Sheaf (Opens.grothendieckTopology Z) RingCat`. They are defeq and NOT syntactically equal,
so any mathlib lemma whose statement mentions `R.obj.obj U` fails to `rw` with
    Did not find an occurrence of the pattern <P> in the target expression <P>
    … The target expression is not type-correct under the `instances` transparency level
— the pattern printed and the target printed being identical. Three cures, in the order to
try them:
* **get the equation from Lean, not from `rw`**: `have h := <the mathlib lemma> <args>`
  elaborates fine, and then `h.trans` / `Eq.trans` / `congrArg` cross the gap because they
  check up to defeq. `refine hleft.trans (Eq.trans ?_ hright.symm)` is the workhorse;
* **`show` the concrete presheaf form**: the whole of `modUnitMul`'s multiplicativity is
  `show (Z.presheaf.map _ a) * (Z.presheaf.map _ b) = Z.presheaf.map _ (a * b)` followed by
  `map_mul`, because `PresheafOfModules.unitHomEquiv`'s inverse is `x ↦ x • s` and the
  composite is a product of restrictions BY `rfl`;
* **when the goal prints as `A = A` and `simp` will not close it, use `rfl`.**
**And never write a numeral at a module type**: `(1 : ↑((modUnit Z).val.obj U))` fails with
`failed to synthesize OfNat`, while the same `1` arrives fine inside a lemma Lean elaborated
itself. If you need the unit section, take it from `unitHomEquiv_apply_coe`'s statement
rather than typing it.
