## YOUR TARGET MAY BE A FREE-FLOATING `sorry` A SEMANTIC MERGE MANUFACTURED — GREP FOR ITS CONSUMERS BEFORE PROVING IT

(2026-07-31, `flt-lean-113`, on `map_add_relPointWeierstrassEquiv` in `X1.lean`.) The
SEVENTH invisibility class above is about a merge that breaks a build. This is its
quiet twin: a merge that leaves the build **green** and the frontier **wrong**, by
orphaning a cut.

The mechanism needs two branches and no mistake by either author. Branch A proves leaf
`L` outright, by a route in another file. Branch B — cut against a copy of the file in
which `L` was still `sorry` — DECOMPOSES `L` into machinery plus a smaller leaf `L'`,
and re-points `L`'s body at them. Both merge cleanly, because they touch different
regions: B's machinery is an insertion, and only `L`'s body conflicts. The resolution
correctly keeps A's PROOF. Now `L'` and all of B's machinery sit in the file with
**nothing above them**, and `L'` is a `sorry` that no declaration in the tree reaches.

Every instrument agrees it is ordinary open work. It emits `declaration uses 'sorry'`,
so the warning set lists it; a source scan finds it; `own.py` correctly reports it
unowned; its docstring says in bold that it is "all that is left of `L`, which is
PROVEN over this leaf alone" — true when written, false after the merge. It drew a
dispatch, which is how this one was found.

**So the first grep of any prover task is not for the target's line number but for its
CONSUMERS**, comment-stripped, across `Fermat/`:

    grep -rn '<target>' Fermat/ | grep -v '<the file and line range it lives in>'

Zero hits outside its own subsection means it is free-floating, and CLAUDE.md forbids
that — so the task is not to prove it.

**Then compare the two routes before repairing, because restoring the consumption is
usually the WRONG repair.** Ask which leaf is left open by each, and whether that leaf
is SHARED. Here the surviving route rests on one leaf that the `Γ₀` consumer needs
anyway, so restoring B's cut would have left that leaf standing *and* added this one.
And check the direction of strength: an `∃`/`Nonempty` producer of *some* isomorphism
does **not** discharge a statement about *this* isomorphism — `e ∘ φ⁻¹` is then merely a
bijection fixing `0`, on which nothing is known — so the orphan was strictly HARDER than
the leaf beside it. A prover would have had to strengthen somebody else's open leaf to
close a declaration nothing consumed.

**The repair that pays: look for the WEAKER shadow the orphaned machinery already
proves, and find the consumer that only ever needed it.** B's dictionary here was a
sorry-free `Equiv`; only the group law was open. `MazurTorsion.lean`'s consumer took the
`≃+` and projected it to `e.toEquiv` on both lines that used it. Publishing the `Equiv`
alone (`nonempty_relPointEquiv_of_weierstrassModel_finiteField`) moved ~400 lines of
proven machinery into the root cone, deleted the free-floating `sorry`, and removed the
shared citation from that consumer's cone — one grep for `.toEquiv` at the call sites is
what found it. **When a bundled conclusion is `≃+`, `≃ₐ`, `≃ₗ`, or a structure, check
what its consumers actually project out.**

