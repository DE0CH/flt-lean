## `simpa using h` can normalise the HYPOTHESIS to `True` and still fail

Symptom, and it reads as nonsense: `Type mismatch: After simplification, term h has type True
but is expected to have type <the goal>`. It means simp PROVED `h`'s statement while leaving
the goal unproved — which sounds impossible, since it is simping both.

It happens when a simp lemma rewrites a TYPE INDEX and thereby unlocks an instance for one
side only. Concrete instance (`MazurTorsion.lean`, `N = 1` branch of
`exists_weilPairing_mu_nondeg_of_coprime`): `h : ((1 : ℕ) : ℤ) • ↑x = 0` where
`x : ↥(E.nTorsion 1)`. Normalising `((1:ℕ):ℤ)` to `1` lets `Submodule.torsionBy_one` rewrite
the submodule to `⊥`, whose carrier is a `Subsingleton`, so `eq_iff_true_of_subsingleton`
closes `h`. In the GOAL the same term sits under the `nTorsion` abbrev, which blocks that
rewrite, so the goal only reaches `x = 0`.

Fix: replace `simpa` with `simp only [<the two lemmas you actually want>] at h` plus an
explicit `exact`. General rule — when a `simpa` fails with `has type True`, the problem is
that simp is doing MORE on one side, so name the rewrites instead of widening them.

