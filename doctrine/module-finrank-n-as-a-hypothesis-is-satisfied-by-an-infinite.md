## `Module.finrank ≤ n` AS A **HYPOTHESIS** IS SATISFIED BY AN INFINITE-RANK MODULE — use `Module.rank`
(2026-07-31, `flt-lean-137`, caught while cutting
`exists_finite_toAffineLine_specialFibre_of_model` in `ModularCurve/X0.lean`.)
`Module.finrank R M` is `Cardinal.toNat (Module.rank R M)`, and `toNat` of an
infinite cardinal is **`0`**.  So `Module.finrank R M ≤ 2` holds for every
infinite-dimensional `M`.
Everyone knows this as a fact about CONCLUSIONS — "a `finrank` conclusion needs a
finiteness side condition" — and it is filed away as a nuisance.  **In a
HYPOTHESIS the sign flips and it stops being a nuisance**: a leaf carrying
`(hdeg : Module.finrank K(f) K(X) ≤ 2)` is quantified over the junk instances
too, so it asserts the conclusion for an `f` with `[K(X) : K(f)]` INFINITE.
That makes the leaf STRICTLY STRONGER than the classical statement it is meant
to be, and possibly FALSE; at best its proof has to open with an argument that
the junk case cannot arise, which is work nobody costed.
**`Module.rank … ≤ 2` in `Cardinal` has no junk value**, says exactly the
classical thing, and additionally *gives* finite-dimensionality rather than
presupposing it.  Use it on the hypothesis side; `finrank` is right on the
conclusion side, where the junk value makes the statement weaker and therefore
safe.  The same asymmetry governs `Nat.card`, `Nat.find`, `sSup` on `ℕ` and
every other `toNat`-shaped truncation: **ask which side of the turnstile the
junk value sits on before choosing the spelling.**
Rider: the junk case really was unreachable here (`K(X)` has transcendence
degree `1` over `K`, so `K(X)/K(f)` is finite for every transcendental `f`), and
that is exactly why it would have survived review — the statement is true either
way, and only the PROOF pays.  Record the reasoning in the docstring when you
pick `rank`, or the next reader will "simplify" it back.
