## "NO FURTHER CLAUSE-SHAPED CUT" IS A VERDICT ABOUT HYPOTHESES — THE QUANTIFIER IS A CUT TOO
(2026-07-31, `flt-lean-242`.) A mature leaf in this tree often carries an
atomicity verdict of the form "no further cut is available — every remaining
hypothesis is consumed by the classical argument, and the conclusion is the input
datum with ONE clause added". That sentence is usually **true and useless**,
because it audits the wrong axis. It asks whether a HYPOTHESIS can be split off.
It does not ask whether the CONCLUSION quantifies over a finite index set.
`exists_eigenform_minimalLevel_of_isUnramifiedOutside` concluded "there is a
quaternionic level datum `𝒮` with `𝒮.S ⊆ badF`". Its verdict was right about
hypotheses — there is no automorphic representation in this tree, so nothing is
splittable off the input side. But the classical argument reaches `𝒮.S ⊆ badF`
by removing the places of `𝒮.S \ badF` **one at a time**, and a finite descent is
in-tree Lean work even when its single step is a citation. The node is now a
proven induction on `𝒮.S.card` over a ONE-PLACE leaf.
**The trade, stated honestly, because it is not a leaf-count win.** One leaf
becomes one leaf. What changes is the SIZE of what is cited: the old leaf owed
the conductor–level dictionary over a whole set plus the finiteness argument that
terminates the descent; the new one owes local–global compatibility and the
newvector statement at a SINGLE place. And the input sharpens with it — the
ramification hypothesis went from `∀ w ∉ badF, ρ unramified at w` to
`ρ unramified at w₀`, because one step needs one place.
**The pattern to look for**, since it recurs wherever a leaf's conclusion is a
containment or a bound over a finite set:
* conclusion mentions a finite set (`S ⊆ bad`, `supp 𝔫 ⊆ …`, `∀ i ∈ s, P i`);
* the classical proof is a descent / induction / one-at-a-time removal;
* the ambient structure lets you build the smaller object cheaply (here
  `U₁Data`'s only constraint on `S` was inherited by subsets, so `eraseS` was
  six lines and the measure `S.card` was three).
Then the loop is yours and only the step is owed. Two Lean-level notes that made
it cheap: pick the measure that needs NO `DecidableEq` in the *statement*
(`𝒮.S.card`, not `(𝒮.S \ bad).card` — `\` forces a `SDiff` instance into the
`suffices`), and put `open scoped Classical in` on the `erase`-based definition,
which then needs `noncomputable`.
**Corollary for anyone writing an atomicity verdict:** say which axis you
checked. "No hypothesis splits off" and "no cut is available" are different
claims, and only the first is usually supported.
