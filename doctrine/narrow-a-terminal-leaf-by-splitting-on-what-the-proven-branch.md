## NARROW A TERMINAL LEAF BY SPLITTING ON WHAT THE PROVEN BRANCH ACTUALLY CONSUMES

(2026-07-31, `Interface.lean`'s Serre local criterion.) When a leaf sits behind a
`by_cases`, the split condition is usually the *natural-language* hypothesis somebody
had in mind ("the inertia image is commutative"), not the thing the proven branch's
proof actually uses. Read the proven branch top to bottom and find where the positive
hypothesis is consumed. If it is consumed once, through a **one-directional
implication**, then **the conclusion of that implication is a strictly weaker splitting
condition** — and re-splitting there moves a real class of cases out of the sorry leaf
for zero mathematics.

The instance: the abelian branch took
`∀ σ τ ∈ localInertiaGroup, Commute (σ₀.toLocal σ) (σ₀.toLocal τ)` and used it in
exactly one step — fed through `hfix : σ₀.toLocal σ = 1 → σ r = r` to get
"inertia COMMUTATORS FIX `r`". `hfix` is one-way: `r` can be fixed by far more than
`ker (σ₀.toLocal)`. Splitting on the commutator condition instead moved the whole class
"`r` lies in the maximal subextension abelian over the maximal unramified one" into the
PROVEN branch, while `ℚ₃(σ₀)` itself stays nonabelian. Separating witness, which is what
makes this a cut rather than a rewording: `Gal ≅ S₃` très ramifiée, `r ∈ ℚ₃(μ₃)` — the
commutator `A₃` fixes `r`, so the new condition holds and the old one fails.

Three things this costs, all of which must be in the same commit:

- **The sorry count does not move.** A narrowing closes nothing. Say so plainly; a
  reviewer counting warnings will otherwise read the commit as no-op.
- **The renamed leaf's earlier FALSITY AUDIT is VOID.** Re-run it. Here it passed with
  no mathematics — only hypotheses were strengthened, so the new statement is *implied
  by* the old, and any counterexample refutes both. That argument is short and it is
  the one to look for first when a restatement only strengthens hypotheses.
- **The old branch's theorem can become FREE-FLOATING.** Rewiring the `by_cases` removes
  its only consumer. Either keep it consumed (a subsumed outer branch, two lines, with a
  comment saying why) or delete it in the same edit — do not merely bypass it.

And check for a *further* widening before stopping, because the answer is often no and
recording that saves the next owner the search: here the descent lemma consumes `hcomm`
only to build `(σ τ) r = (τ σ) r`, which looks weaker and is provably equivalent, since
the cyclotomic character kills commutators and so the commutator fixes `ζ^a · r` iff it
fixes `r`. That condition is optimal for that machinery; any further widening has to
come from a different tool.

