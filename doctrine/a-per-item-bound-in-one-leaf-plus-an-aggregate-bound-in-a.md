## A PER-ITEM BOUND IN ONE LEAF PLUS AN AGGREGATE BOUND IN A SIBLING IS A SQUEEZE — one of the two is free
(2026-07-31, `flt-lean-222`, `ModularCurve/X0.lean`.)  Two sibling leaves in one
subsection routinely bound the SAME quantity, one item at a time and one in aggregate.
When they do, and when the reverse per-item bound is available for nothing, the aggregate
bound FORCES the per-item bound and the leaf asking for it is asking for something it
already has.
Here `exists_cuspAboveDivisor_neron` asked, per divisor `d`, for a cusp `x_d` with
`[κ(x_d) : ℚ] ≤ φ(g_d)`, while the sibling `sum_residueQDegree_compl_le_sum_totient`
bounds `∑_{p ∈ X∖Y} [κ(p) : ℚ] ≤ ∑_d φ(g_d)`.  The reverse per-item bound is free from
the leaf's OTHER conjunct — a primitive `g_d`-th root of unity in `κ(x_d)` gives
`φ(g_d) ≤ [κ(x_d) : ℚ]` by `minpoly` — and the `x_d` are distinct, so
    ∑_d φ(g_d)  ≤  ∑_d [κ(x_d) : ℚ]  ≤  ∑_{p ∈ X∖Y} [κ(p) : ℚ]  ≤  ∑_d φ(g_d)
collapses to termwise equality (`Finset.sum_eq_sum_iff_of_le`).  The upper bound is a
theorem, not an obligation.
**WHAT MAKES THIS WORTH DOING IS NOT THE COUNT — IT IS THAT A NAMED CLASSICAL INPUT LEAVES
THE TREE.**  The trade is `1 -> 1`, so every frontier scan reports nothing.  What changed
is that `[κ(x_d) : ℚ] ≤ φ(g_d)` *is* Deligne–Rapoport's statement that the `φ(g)` geometric
cusps above a fixed number of sides form a SINGLE GALOIS ORBIT — and the sibling's own
docstring already recorded that ITS degree form "keeps the count and drops the
transitivity".  So after the cut **no leaf anywhere asks for the orbit statement**.  Two
leaves were paying for one citation and only one of them needed it.
**The check, and it is a read of two docstrings rather than a proof attempt.**  For each
open leaf in a subsection, write down which classical input it names.  If two name the
same one, ask whether either can be derived from the other plus something free.  The tell
in this instance was verbal and not structural: both docstrings cited DR §V.5, and one of
them said in as many words that it had dropped the half the other still carried.  No
duplicate-declaration scan, no `dupstmt.py`, and no frontier count can see this — the two
statements share no identifier and are about different objects (a point, and a sum over
all points).
Four riders, three of them cheap and one of them the price:
* **The other three conjuncts went the same way and none of them was DR either.**
  Membership in the cusp locus is a FIELD of the classifier (`cuspClassify_mem`);
  `residueQDegree ≠ 0` is `one_le_residueQDegree_of_notMem_range`, i.e. properness plus
  Jacobsonness; `N = 0` is vacuous because `Nat.divisors 0 = ∅`.  **Before proving a
  multi-conjunct leaf, price each conjunct separately against what is already in the
  file** — here four of five were free and the fifth is the whole of the mathematics.
* **When an audit says "a successor who adds X can derive it and should", add the WEAKEST
  clause that does, not X.**  The audit asked for INITIALITY on `CuspClassifier` to get
  injectivity.  What injectivity needs is only that the number of sides is an invariant of
  the cusp, which is one clause (`sides_unique`) rather than a universal property, is a
  consequence of DR's theorem so it cannot make the structure unsatisfiable, and is free
  to anyone holding the model.  Adding a clause to a structure appearing in a leaf's
  CONCLUSION makes that leaf HARDER, so it is only justified when the same leaf sheds
  strictly more than it gains — say which, in the docstring, or the next reader cannot
  check it.
* **The price was a RELOCATION, because the sibling was declared below.**  Do it as its own
  commit with the line-multiset receipt (`Counter(new) == Counter(old)`), and check first
  that the moved block's STATEMENT names nothing declared in the region it jumps — a bare
  `sorry` leaf is the safest possible thing to hoist, since its body cites nothing at all.
* **Mark the overtaken audit points IN PLACE, do not delete them.**  Two of the three
  points of that leaf's FALSITY AUDIT stopped being true of the new arrangement (one asked
  for injectivity separately; one explained why `hN` was absent).  Both are still the
  reason the NEW leaf is shaped as it is, so each got an `OVERTAKEN` header and kept its
  text.  An audit point that is silently deleted gets re-derived by the next agent from
  the same evidence.
### `simp` cannot refute a Finset-subtype membership — it PROVES it
Same task, one round trip.  For `d : ↥(s : Finset α)`, `d.2 : ↑d ∈ s`, and `by simp`
applied to that hypothesis rewrites it to `True` via `Finset.coe_mem` — which is correct
and useless, because the contradiction one wants at `s = Nat.divisors 0` comes from
unfolding `s`, not from the membership.  So `absurd d.2 (by simp)` fails with an unsolved
`⊢ False` that looks like a simp-set gap.  Go through the membership CHARACTERISATION
instead: `(Nat.mem_divisors.mp d.2).2 rfl : False`, since `Nat.mem_divisors` carries the
conjunct `n ≠ 0`.  The general form: to derive `False` from an element of an empty
`Finset`-subtype, rewrite the FINSET, never simp the membership.
