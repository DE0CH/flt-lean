## A RELOCATION'S COST AND ITS PAYOFF ARE MEASURED AT DIFFERENT DECLARATIONS — AND A PREDICATE'S REAL COST IS ITS **PRODUCER'S** HYPOTHESES
(2026-08-01, `flt-lean-341`, the proposed extraction of `HardlyRamified/Family.lean`'s
Raynaud cone downward so that `HardlyRamified/Threeadic.lean` could close its two
`connected_locus_*_of_hopf_package` leaves.)
The standing relocation checklist — *measure the block on the current base, walk the
import closure for a cycle, diff the hypotheses, count concurrent editors* — is right
and it was run. Two of its four items came back GREEN and the plan still died, in a
way the checklist as written does not surface.
**1. THE BLOCK YOU MEASURE IS NOT THE BLOCK THAT PAYS.** The obvious thing to measure
is the theorem whose STATEMENT you want, and here that is
`isMultiplicativeType_corner_of_inertiaLevelOneFlag` — coefficient-free, intrinsic on
the corner Hopf algebra, and a transitive decl/use closure of **6 declarations and 489
lines**, acyclic, carrying its own two open leaves so the move is leaf-count-neutral.
Cheap by any measure. But the consumer's leaves are about the connected LOCUS OF
POINTS, and the bridge from `IsMultiplicativeType` of the corner to any points-level
statement is `connected_point_smul_eq_cyclotomicCharacter_smul_of_hopf_package`, whose
closure is **105 declarations and 5752 lines** — twelve times bigger, and the number
that decides the plan. The task prompt costed it at "~2600 lines", which is neither.
**So measure the closure of the theorem you will actually CITE at the call site**, not
of the theorem whose name matches the mathematics you have in mind. Those are routinely
different declarations in this tree, because the intrinsic statement and the
representation-level statement are cut apart on purpose.
**2. "COEFFICIENT-FREE" IS A PROPERTY OF THE STATEMENT, NOT OF REACHABILITY — GREP FOR
THE PREDICATE'S PRODUCERS.** `HasInertiaLevelOneFlag p G` is genuinely intrinsic: a
chain of inertia-stable `AddSubmonoid`s of the geometric points with order-`p`
quotients, mentioning no coefficient ring. That is exactly what makes it look free to
supply. It is not: **it has exactly ONE producer in the whole tree**
(`hasInertiaLevelOneFlag_of_hopf_package`), and that producer runs through
`exists_levelOneFlag_space_of_charpoly` and therefore carries `χ₁`, `χ₂`, `hchar`,
`[Algebra R (AlgebraicClosure ℚ_[p])]`, `hZinj`, `hRinj` — GLOBAL reducibility of `ρ`
by two continuous characters. The consumer had only RESIDUAL reducibility. So the
hypothesis diff of the theorem you want can come back CLEAN while the theorem is still
uninstantiable, because the cost has been pushed one level down into the predicate.
The check is one command and it belongs beside the hypothesis diff:
    grep -n '<Predicate>' <file> | ...   # separate CONCLUSIONS from `h…` BINDERS
Six of the seven occurrences here were binders. A predicate that appears in one
conclusion and six binders is a bottleneck, and its producer's binder list is the
predicate's true price.
**3. A TRANSITIVE IMPORT PATH THROUGH A NON-PUBLIC EDGE RE-EXPORTS NOTHING.** The
prompt asserted that the extraction was "unconstrained on the `Family` side, since
`Family` already reaches `Threeadic` transitively, so ANY new module that `Threeadic`
imports is automatically visible to `Family` too." False: `Family` reaches `Threeadic`
only through `Interface.lean:436`, which is a plain `import`, so nothing behind that
edge is re-exported. `Family.lean:3527` says so about `finite_points_of_hopf_order` in
as many words. **Reachability in the import GRAPH is not visibility**; compute the
closure over `^public import` when the question is what a module can NAME.
**AND WHEN THE PLAN DIES, THE RESIDUE IS THE DELIVERABLE.** What the survey left
behind is worth more than the extraction would have been: the missing piece is a
SECOND, `hchar`-free producer of the predicate, and in the consumer's own setting it is
constructible from binders it already holds — the residual sub character there is `ω`,
whose values lie in the PRIME FIELD, which is precisely the "level one" input. Naming
that construction, with the numbers and the refutation, converts an unbounded
relocation into a bounded new leaf. Record it on the LEAF, dated and stamped with the
sha, not only in a report.
