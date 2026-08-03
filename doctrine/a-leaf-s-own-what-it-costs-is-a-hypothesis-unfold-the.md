## A LEAF'S OWN "WHAT IT COSTS" IS A HYPOTHESIS — unfold the DEFINITION first

(2026-07-31, flt-lean-110.) `exists_finset_isUnramifiedAt_hilbert_of_notMem` carried a
docstring saying it costs the CONVERSE of `MinkowskiUnramified.lean`'s
`isUnramifiedAt_of_inertia_le_fixingSubgroup` ("`w` unramified in `L/F` ⟹ `I_w` fixes
`L` pointwise"), that the converse is absent from the pin, and that it is SHARED with
`finite_hilbertInertiaOutsideSubgroups` — so "the two leaves are natural companions and
are best given to ONE owner."

Every factual clause was true. The conclusion was wrong twice over. The converse is
expensive (it needs local–global compatibility of ramification indices, which this tree
does not have) and **it is not needed at all.** `localInertiaGroup v` is DEFINED as the
inertia subgroup of the maximal ideal of `IntegralClosure 𝒪ᵥ Kᵥᵃˡᵍ` — "σx − x ∈ 𝔪 for
every integral x" — so "inertia fixes `α`" is checkable DIRECTLY, with no discriminant,
no ramification index and no dictionary: `α` and `σα` are congruent roots of
`minpoly ℤ α` in a local domain, and Hensel-free simple-root separation forces them
equal at every place off the finitely many dividing `(minpoly ℤ (P'(α))).coeff 0`. The
identical retraction had been recorded at the `ℚ` level three days earlier on the twin
leaf in `Modularity/Patching.lean`, and simply was not transferred.

Two rules, the second the one that costs releases:

- **Before buying a dictionary lemma a docstring names, unfold the definition of the
  object it is about.** A "missing dictionary" is often a translation between two
  spellings that the proof never has to cross.
- **A leaf-PAIRING recommendation ("give these two to one owner, they share `X`") is a
  claim about `X`, and it dies with `X`.** Re-derive it; do not inherit it. Here the
  pairing would have chained an already-closable leaf to a genuinely hard one and hidden
  that the hard one stands alone.

Corollary for TWIN leaves generally: this development is full of `ℚ`-level/`F`-level
twins whose docstrings were written by copying. **A correction applied to one twin is
not applied to the other** — nothing propagates it — so when you touch a leaf whose
docstring names a twin, read the twin's CURRENT docstring, not the sentence your leaf
quotes from it.

