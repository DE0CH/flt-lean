## NAME THE WITNESS — an existential leaf pushes hypotheses onto every consumer

(2026-07-31, `X1.lean`.) When a proven theorem is stated as `∃ g, P g` but its
proof is literally `⟨someExplicitTerm, …⟩`, the existential is not abstraction —
it is a **leak**. Every consumer must either `choose` or carry `g` and `P g`
as extra hypotheses through its own statement, and a *sorry leaf* that does the
latter is now quantified over ALL witnesses when only one was ever meant.

That is not merely inelegant; it manufactures an unwritten proof obligation.
`integral_Ioi_one_sub_frickePartner_ne_zero_x1TwentyFive` took a bare cusp form
`g` plus the Fricke functional equation as hypotheses, because
`exists_frickeInvolutionOn` gave it nothing better — and its docstring then had
to record, under "assumptions I am recording rather than resolving", that this
was sound *because `g` is pinned by the relation: a holomorphic function on the
connected upper half plane is determined by its values on the imaginary axis*.
That argument is correct and was never written in Lean. Naming the witness
(`frickeSlashOn N hN h1 h0 f`, which the proof already produced) **deleted the
obligation instead of discharging it**, dropped two hypotheses from the leaf,
and changed what a prover owes from "reason about an unknown partner" to
"compute the `q`-expansion of a named form".

So: **state the named form as the theorem and the existential as its two-line
corollary**, keeping the corollary only where a consumer genuinely does not care
which witness it gets (here `cuspFEPairOn`, which `choose`s). The cost is one
declaration; the check is whether the proof of the existential is an `⟨_, _⟩`
with no `obtain` above it. `X0.lean`'s `axisRestrict_one_div_eq_frickeSlash` is
the same pattern on the `Γ₀` side and predates this note — the `Γ₁` mirror had
simply not been brought into line.

