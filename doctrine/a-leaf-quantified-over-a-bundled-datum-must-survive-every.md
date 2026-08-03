## A LEAF QUANTIFIED OVER A BUNDLED DATUM MUST SURVIVE EVERY *RELABELLING* THAT DATUM ADMITS

(2026-07-31, `range_base_atkinLehner_cusp` in `ModularCurve/X0.lean` — refuted the day
after it was cut, by two instances of ITSELF.)

`∀ C : SomeStructure, P C` is only as strong as the structure's fields make it. This file
already records the PINCH test for that shape — perturb the *object* the structure
describes and see which clauses survive. There is a second, cheaper and much more easily
missed perturbation: **leave the object alone and permute the INDEXING.** A structure whose
fields are a family `κ : ι → (something about X)` plus constraints that are all invariant
under reindexing admits `C ∘ σ` for every `σ` in a group of permutations of `ι`, and a
conclusion that mentions a *specific* map `ι → ι` is then provable only if that map is
central for the whole group.

`IsX0Compactification.CuspLocus` indexes the cusps of `X_0(N)` by `N.divisors` and pins the
labelling only through `degree d = φ(gcd(d, N/d))`. So `C ∘ σ` is again a `CuspLocus` for
every `σ` preserving that function — `cover` because `σ` is a bijection, `disj` because it
is injective, `ratPoint` by handing back `σ.symm d`, `degree` by hypothesis. The leaf
asserted `w (cusp_d) = cusp_{N/d}`, i.e. that `w`'s cusp permutation is `ι : d ↦ N/d` in
EVERY labelling — which forces every admissible `σ` to commute with `ι`. At `N = 4` the
three values of `φ(gcd(d, 4/d))` are all `1`, so every permutation of `{1, 2, 4}` is
admissible, and the leaf at `C` (`d = 2`) with the leaf at `C ∘ (1 2)` (`d = 1`) gives
`c_2 = c_4` against `C.disj`. **Both are instances of the leaf, so the refutation assumes
nothing about `w` at all** — which is the cheapest possible shape of refutation and the one
to look for first on a `∀ datum` leaf.

**Why it survived the audit it already had.** The docstring carried a paragraph headed
*"THE STATEMENT IS ROBUST TO THE INDEXING CONVENTION"*, correctly observing that `CuspLocus`
fixes no convention and that `φ(gcd(d, N/d))` is symmetric under `d ↦ N/d`. Every clause was
true. The inference was not: it varied the labelling **only along the involution the leaf
was trying to establish**, which is exactly the relabelling that cannot detect the problem.
That is the same failure as *A COUNTEREXAMPLE IS ONLY AS STRONG AS THE HYPOTHESIS LIST* below
and *vary the parameter you did not think of as a parameter*, arriving through a symmetry
argument — and a symmetry argument reads as more conclusive than a witness search, so it is
worse.

**The mechanical test, and it costs one careful read of the structure.** List the fields.
Cross off the ones that are pointwise in the index (`K`, `κ`, `comm`, the instances) and the
ones invariant under bijections (`cover`, `disj`, `ratPoint`). What remains — here just
`degree` — is the whole of what pins the labelling. Then compute the group it leaves: the
permutations preserving that invariant. If the conclusion names a map on the index set,
check it is central in that group. **Do this before writing the leaf**, and record the group
in the docstring; it is the datum's real automorphism group and every later `∀ C` statement
in the file has to respect it.

**The repair is usually a hypothesis, not a restatement.** Adding "the fibre of the pinning
invariant through `d` is exactly `{d, N/d}`" (`hrigid`) makes every admissible `σ` restrict
to that pair, where it is central for trivial reasons. It is sharp — the refutation runs at
every `d` where it fails — it is DECIDABLE, and the sole consumer discharged it with
`decide`, so no signature above the leaf moved. The alternative repair, existentially
quantifying the datum (`∃ C, ∀ d, …`), is the honest general statement and is strictly
weaker; prefer the hypothesis while every consumer satisfies it, and say in the docstring
which levels would need the existential form. Adding a hypothesis is a restatement, so the
old faithfulness audit is VOID — but in this direction re-running it is short, since a
strengthened hypothesis can only shrink the class of counterexamples.

