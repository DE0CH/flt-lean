## Two unification traps around `Localization` and `MvPolynomial`
(2026-07-31; each one cost a multi-minute `whnf`/`isDefEq` timeout that reads as
"my proof is wrong" when in fact the statement was unusable as written.)
**1. `MvPolynomial.aeval (R := ℤ)` is UNUSABLE against a localisation.** There are
two `Algebra ℤ` instances in play: a generic `[CommRing T]` lemma carries
`Ring.toIntAlgebra`, while instance search at a `Localization M` finds
`OreLocalization.instAlgebra`. They are propositionally equal and **syntactically
different**, so `rw` fails between two terms that print identically; and under the
module system the error even ends `definitions were not unfolded because their
definition is not exposed: OreLocalization.instAdd`, so no amount of `unfold` gets
you out. The fix is to avoid `Algebra ℤ` entirely — evaluate integral polynomials
through `MvPolynomial.eval₂Hom (Int.castRingHom T)`, which depends only on the ring
structure. `intEval` in `MoretBailly.lean` is that wrapper, with its API
(`intEval_rename`, `intEval_bind₁`, `ringHom_intEval`, `algHom_intEval`,
`intEval_eq_aeval_map`).
Corollary: keep a RingHom version *and* an AlgHom version of any "the map commutes
with evaluation" lemma. `φ (…)` for an `AlgHom φ` and `↑φ (…)` for the same map
coerced to a `RingHom` are different terms for `rw`, so a single version leaves you
stuck at exactly the last step.
**2. A lemma about `Localization.Away x` must take `x` as a PARAMETER with a
defining equation.** Stating the conclusion as
`∃ ψ : Localization.Away (Ideal.Quotient.mk I (map a)) →ₐ[K] T, …` and then
instantiating it where the goal says `Localization.Away (integralSystemClass f K a)`
sends the unifier down into the `OreLocalization` quotient and it does not come
back — `timeout at whnf`, ~4 minutes at a million heartbeats, for what is a single
delta-unfolding. Write instead
    (x : MvPolynomial (Fin n) K ⧸ I) (hx : x = Ideal.Quotient.mk I (map a))
    … ∃ ψ : Localization.Away x →ₐ[K] T, …
`subst hx` recovers the concrete form inside the proof, the *type* matches
syntactically at every call site, and `hx` is discharged by `rfl` — a defeq check
on the ELEMENT, which is cheap, instead of one buried under a quotient type.
**Reconfirmed 2026-07-31 on `exists_neronExtension_atSpecialGenericPoint`,
with the ratio now WORSE and so the rule stronger: 45 s against ~20 min.**
`X0.lean` no longer elaborates in 8 minutes — measure it yourself, but budget
20 and plan for at most a handful of real-file verifies per run. The whole of
that leaf (~90 lines, five mathlib mechanisms) was developed in the abstract
`example` and pasted in with three trivial renames. **The corollary is a
scheduling one: do not start a real-file build and then keep editing the file
— `lean` reads the source at start, so the result is stale on arrival and you
have burned 20 minutes.** Reach the final form in the scratch first.
