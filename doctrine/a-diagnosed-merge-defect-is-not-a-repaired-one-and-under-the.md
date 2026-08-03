## A DIAGNOSED MERGE DEFECT IS NOT A REPAIRED ONE — AND UNDER THE LOOP NOBODY FOLLOWS UP
(2026-08-02, `flt-lean-192`, `ModularCurve/RelativePicard.lean`.)  The section
above and the memory `flt-both-rival-cuts-landed` describe this file's
double-cut defect **exactly** — four open leaves where two suffice, the winning
cut's proven assembly left with zero consumers, and the tie-break to use.  That
memory was written on 2026-08-01, by an agent that had clearly read the file.
The defect was still there on 2026-08-02: `exists_relPicZeroSubgroup` still
called the 2026-07-30 cut, `exists_relPicZeroSubfunctor` still had zero
consumers, and the frontier still carried both pairs.
So the standing rule *A FALSITY AUDIT THAT PRESCRIBES A CUT MUST BE PERFORMED*
applies verbatim to a MERGE diagnosis, and for the same reason: **an agent that
writes the diagnosis and stops has created a task that will never be
dispatched**, because no frontier scan can see it (every one of the four leaves
is an honest `sorry` in a green module) and the loop has no notion of "known
defect".  If you find one, repair it in the same run; the repair here was one
verified `lake build` and about ninety minutes.
**And the repair is cheap in a specific way worth knowing**, because the thing
that looks expensive — re-proving the winner's assembly, which the merge had
dropped — is not.  Transporting a group structure along an injective natural
`incl` whose image is closed under the operations is: `choose` the three
operations out of the three closure clauses, then discharge each axiom as
`hinj` applied to `simp only [<the three choose-specs>, <the naturality of the
ambient operation>]`.  Nine fields, one line each, first compile.  The
ingredients (`addPoint_assoc`, `addPoint_comm`, `zeroPoint_addPoint`,
`negPoint_addPoint`, `pre_addPoint`, `pre_zeroPoint`) were all PROVEN in the
same file, ~4000 lines above, and the docstring of the declaration needing them
already said so.
**Keep the loser's PROVEN infrastructure consumed rather than deleting it.**
`RelGroupSchemeStruct` and `toAbelianSchemeStruct` existed only for the losing
cut, so the naive deletion takes them too — and they are exactly the right
shape for the winner: build the group structure WITHOUT properness, then close
the gap.  Routing the new transport through them deletes nothing and leaves
nothing free-floating.  Delete only what has no consumer AFTER the rewiring
(here `IsRelPicZeroIncl`, which existed to state the two dead leaves).
### THE TIE-BREAK THAT ACTUALLY DECIDES: which leaf is IMPLIED by the other
The recorded tie-breakers — fewer OPEN leaves, named beats anonymous, already
integrated and consumed — did not separate these two cuts: both had two named
leaves, and "already integrated" pointed at the **loser**.  What separates them
is a question about the STATEMENTS, and it is decidable:
> **Does a witness of cut A's leaf yield a witness of cut B's leaf?**  If so, B's
> leaf is weaker, and B is the cut to keep whatever the consumer graph says.
Here `exists_relPicIdentityComponent` asks for the three closure clauses as bare
EXISTENTIALS, where `exists_relPicZeroGroupScheme` asked for `add`/`zero`/`neg`
as OPERATIONS plus six group axioms and two strict homomorphism equalities — and
a witness of the second gives a witness of the first by taking `G.zero g`,
`G.add p q`, `G.neg p`.  None of those axioms was ever about the object being
cut out; they are the ambient group's axioms restricted to a subgroup, i.e.
exactly the work the transport above does once for everybody.  **Write the
implication out in the deletion note**: it is the receipt that the deletion
cannot have made anything harder, and it is two lines.
### A `∀`-CLAUSE OVER TEST OBJECTS IS USUALLY ITS OWN INSTANCE AT THE TAUTOLOGICAL POINT
Same file, same run, and it is the cheapest kind of leaf-sharpening there is.
`exists_relPicIdentityComponent`'s Abel–Jacobi clause was
`∀ T g x, ∃ p, incl T g p = aj T g x`, and its own section heading argued at
length why that family is reachable — *"the universal point is an `X`-point of
`Pic` … and every other `aj T g x` is obtained from it by `RelPoint.pre` — so
'a connected family through the identity lies in the identity component' applies
to ONE point and then propagates."*  **That paragraph is a proof and it was
prose.**  Written down (`img_of_img_selfPoint`, eight lines) it lets the leaf ask
for the single membership at the tautological point instead of the family.
The two ingredients were `relPicSelfPoint` and `relPicSelfPoint_pre` — *in the
same file, 3000 lines above*, written for an unrelated consumer, and never
connected to this clause.  So the check is: **whenever a leaf's conclusion
quantifies over all test objects in a functor-of-points development, grep the
file for its tautological point and its `pre` lemma before accepting the `∀`.**
This is the dual of `flt-forall-test-object-leaf-reduces-to-universal` (which
reduces a `∀`-IDENTITY to the universal instance); here it is a `∀`-EXISTENTIAL,
and the reduction goes through the naturality the leaf already concludes.
Two accounting notes.  The count does not move (`1 → 1`), so say what got
smaller.  And the leaf's faithfulness audit transfers **only if you check the
instance**: it survives here because the audit's own witness against dropping
the clause (`J = S`, `jstr = 𝟙 S`) is refuted at `T = X`, `g = strX`, which is
precisely the instance that survives.  Had the audit's witness died only at some
other `(T, g)`, the weakening would have admitted it and the leaf would have
become junk-satisfiable.  Check WHICH instance the audit uses.
