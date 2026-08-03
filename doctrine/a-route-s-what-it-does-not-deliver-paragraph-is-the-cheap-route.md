## A ROUTE'S "WHAT IT DOES NOT DELIVER" PARAGRAPH IS THE CHEAP ROUTE — PROVE THAT FIRST
(2026-07-31, `flt-lean-135`, closing `exists_fundamentalCharacter_of_relIndex_localInertiaGroup`
in `FreyCurve/MazurTorsion.lean`.) A mature leaf's docstring often ends with a
fully worked route and then a paragraph of the form
> *What that route does NOT deliver as it stands is `<clause>`. The extra
> ingredient is exactly `<structural fact>` — worth cutting out as its own lemma
> when this leaf is attacked.*
Read that as an ORDERING instruction, not as an afterthought. Here the route was
"build one big finite quotient `(χ, θ, I_N/J)`, take its cyclic generator `g₀`,
and define `ψ σ := χ(g₀)^{k/e}`", and the residue was torsion-freeness of
`T = I_N/P_N`. **Proving the structural facts about `T` FIRST made three quarters
of the route unnecessary**: the level-`e(N−1)` tame character `θ` was not needed,
`exists_localInertia_tameCharacter_orbit` was not needed, and no
well-definedness-modulo-`e(N−1)` bookkeeping appears anywhere. The finite
quotient shrank to one Lagrange step in a group of order `e`.
The reason is general and worth the check every time: **a route through ONE finite
quotient can never see a statement about the infinite group, so the residue it
leaves is always the hard half; whereas the structural facts, once proven, usually
make the finite quotient nearly free.** Ask which direction the leaf's own
docstring is pointing before following it.
**The two structural facts here were each a few lines, and neither is in the
audit's list of available inputs.** Both come from ONE observation —
`ArtinConductor.lean` builds `P_v` as the intersection of the kernels of the tame
characters `θ_z` (`mem_subgroupOf_wild_of_forall_mem_tameLevel`), so a statement
"`x ∈ P_v`" is "`θ_z(x) = 1` for every tame generator `z`":
* **`T` IS ABELIAN** — every `θ_z` lands in `rootsOfUnity`, which is COMMUTATIVE,
  so every commutator dies in every `θ_z`. Three lines.
* **`T` IS TORSION-FREE** at exponents prime to the residue characteristic — given
  `t^n ∈ P_v` and a tame generator `z` of exponent `m`, take an `n`-th root `z'` of
  `z` in `Kᵥᵃˡᵍ` (algebraically closed, so it exists), note `z'` is again a tame
  generator of exponent `n·m`, and `θ_z(t) = θ_{z'}(t)^n = θ_{z'}(t^n) = 1`. Forty
  lines, and it is the one step that genuinely uses the algebraic closure — the
  individual finite levels cannot see it, which is exactly why a finite-quotient
  route cannot produce it.
**Generalisable: when a group is DEFINED as an intersection of kernels, every
property of the common target transfers to the quotient for free.** Commutativity,
exponent, torsion — check the target's algebra before believing any of them is
hard. In this development that pattern recurs (`tameLevel`, `tameFixingSubgroup`,
`swanExponent`'s filtration), and the targets are all abelian.
Corollary about SHAPE: state the result over an ABSTRACT character. The general
form here — arbitrary number field `K`, arbitrary place `v`, arbitrary
`CommGroup`-valued `chi : I_v →* A` that kills `P_v` and is surjective — is where
all the work lives, and the `ℚ`/`χ̄_N` instantiation is fifty lines with two side
conditions (`χ̄(P_N) = 1` because `P_N` is `(N−1)`-divisible and `#(ZMod N)ˣ = N−1`;
surjectivity is `A₀-1`). It is then reusable at every place and every character.
### `Subgroup.exists_pow_le_index_mem`: pigeonhole beats `normalCore`
"`g^{e!} ∈ H` for every `g`, when `[G : H] = e`" is the standard way to get
`P_v ≤ J` from the index alone, and the standard proof goes through
`H.normalCore = ker (toPermHom G (G ⧸ H))` plus `Nat.card (Perm α) = (Nat.card α)!`.
**Mathlib has neither `Subgroup.index_normalCore_dvd_factorial` nor `Nat.card_perm`**
(only `Fintype.card_perm`), so that route is ~40 lines of `Fintype`/`Nat.card`
bridging. Pigeonhole is shorter and needs no normality at all: among
`⟦u^0⟧, …, ⟦u^e⟧` in the `e`-element coset space two agree, giving `0 < d ≤ e` with
`u^d ∈ H`; then `d ∣ e!` (`Nat.dvd_factorial`) finishes. `N ∤ e!` is
`Nat.Prime.dvd_factorial` (`p ∣ n ! ↔ p ≤ n`) — do not try to factor `720`.
### A FAILING TACTIC BURNS THE DECLARATION'S HEARTBEAT BUDGET, AND THE TIMEOUT SURFACES SOMEWHERE ELSE
Measured twice in this run and it cost a round each time. `maxHeartbeats` is
counted PER DECLARATION, so one `rw` chain that fails deep inside a 150-line proof
leaves the rest of that proof running on fumes — and the error you are shown is a
**`(deterministic) timeout at isDefEq`** on a later, entirely innocent line (here
`obtain ⟨t, ht⟩ := hchisurj a`, a one-line destructuring), plus a second
`timeout at whnf` reported at the declaration's own header line. Neither names the
real fault.
So: **fix the FIRST error in a declaration and re-run before reading any timeout
in the same declaration**, and do not add `set_option maxHeartbeats` in response to
a timeout you have not localised — it just moves the report.
The same effect distorts every timing you take: this file went from **4m52s to 20s**
on the run that fixed the last error, with no other change. **Elaboration time
measured while a declaration is red is not evidence about its cost when green** —
so do not price a scratch loop, or decide to split a file, off a failing run.
### Three small Lean facts from the same proof
* **`{ inferInstanceAs (Group X) with mul_comm := h }` does not build a `CommGroup`** —
  it reports `inferInstanceAs failed, expected type contains metavariables` followed
  by `expected structure`. Do not fight it: `Commute a b` is *definitionally*
  `a * b = b * a`, so a proved `∀ a b : X, a * b = b * a` is directly a `Commute`
  term, and `Commute.mul_pow` / `Commute.mul_pow` give everything `mul_pow` would.
* **`omega` cannot prove `c * e = k` from `k = e * c`** — both are variables, so it
  is nonlinear. `rw [hc, Nat.mul_comm]`.
* **`congrArg Subtype.val` crosses the `IntegralClosure` action** — `(σ • x).val` is
  `rfl`-equal to `σ • x.val`, so `exact congrArg Subtype.val h` works exactly where
  `rw [IntegralClosure.coe_smul]` fails with "did not find an occurrence of the
  pattern" on a goal that displays it.
### The result, and the cheap way it was certified
`exists_fundamentalCharacter_of_relIndex_localInertiaGroup` came back
`[propext, Classical.choice, Quot.sound]` — FULLY axiom-clean, not merely
direct-sorry-free — so the whole `ArtinConductor.lean` wild-inertia block it rests
on (`exists_pow_eq_of_mem_wildInertiaGroup`,
`exists_localInertia_generator_mod_pow_wildInertiaGroup`, `tameCharacter`,
`mem_subgroupOf_wild_of_forall_mem_tameLevel`) is sorry-free too. **Those
declarations' own docstrings still describe some of their inputs as "the one open
leaf"; they have since been proven and the prose was not updated.** That is the
standing "a docstring's absence claim is dated evidence" rule, and `#print axioms`
is what settles it in seconds — see the correction at the top of this file about
running it from an importer.
