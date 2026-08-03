## A "CONSTRUCT THE OBJECT" LEAF SPLITS ONCE THE REPRESENTABILITY THEOREM IS UPSTREAM — AND THE SPECIALISATION'S HOME IS NOT THE THEOREM'S HOME
(2026-07-31, `flt-lean-136`, cutting `exists_abelianScheme_addEquiv_pic` in
`ModularCurve/HyperellipticJacobian.lean` — "build the Jacobian of `y² = f(x)` as an
abelian scheme over `ℚ` and identify its `ℚ`-points with `Pic⁰`".)
A leaf of the shape *construct object `O`, then compare it with something I already have*
is usually two jobs, and the standing advice is to cut it that way.  What decides whether
the cut is cheap is a question nobody asks first: **is there already a GENERAL existence
theorem for `O` upstream, over an arbitrary base?**  If there is, the construction half
collapses to *construct the INPUT of that theorem*, which is normally a much smaller
object — here the Jacobian became the CURVE, and Grothendieck representability (FGA 232,
BLR 8.2/1) left the file altogether.
**THE TRAP THAT ALMOST HID IT: the theorem's `SpecQ` specialisation lived in a module this
file may not import, and the general form did not.**  `exists_relPicZeroOf` is in
`X0.lean`, and `HyperellipticJacobian.lean` carries a comment — earned the hard way on
2026-07-31, when the edge took the WHOLE project down with `build cycle detected` — saying
that importing `X0.lean` closes a loop (`X0 → IsogenySignature → HyperellipticJacobian`).
So "the representability theorem is unreachable from here" is the natural reading, and it
is wrong: `X0.lean`'s own docstring says the declaration is *"a ONE-LINE INSTANCE, and that
is the whole point"* of `Fermat.exists_relPicZero` in `ModularCurve/RelativePicard.lean`,
which is universe-polymorphic, over an arbitrary base, upstream of everything, and **was
already in this file's import closure** — non-publicly, so invisible to a statement.
Promoting that edge to `public` added ZERO modules to any cone (measured: closure size 20
before and after) and made the cut expressible.
**So when a theorem you need sits in an unimportable module, check whether it is a
specialisation.** In this development the general form is routinely in a small upstream
module and the named specialisation in the giant consumer, precisely because two consumers
at two bases would otherwise force two sorried copies — several `X0.lean` docstrings say so
in as many words. `grep` for the CONCLUSION's shape, not for the name you know.
**AND VERIFY THE NEW EDGE BY TRANSITIVE CLOSURE, over the whole tree.** Ten lines of Python,
seconds to run, and it must ASSERT that every visited module's file exists — a swallowed
`FileNotFoundError` truncates the walk and manufactures the "no cycle" answer you were
hoping for. The direct-edge check is what failed in the incident above.
### The linkage between the two halves can be a bare `RingEquiv`, because `ℚ` is the prime field
The halves have to be joined by a statement of the form *`X` is the model OF `D`*, and the
obvious spelling is an `≃ₐ[ℚ]` of function fields.  That spelling costs a construction:
`Scheme.functionField` is a STALK, and this pin has no `Algebra ℚ ↥X.functionField`
instance, so it would have to be built before the leaf could even be STATED.
It is not needed.  **`ℚ` is the prime field of characteristic zero, so every ring
homomorphism between `ℚ`-algebras is automatically `ℚ`-linear**, and `Nonempty (D.F ≃+*
↥X.functionField)` says exactly as much as the algebra version.  The same weakening is free
over `𝔽_p`.  Generalisable: **before building an algebra structure to state a linkage, check
whether the base is a prime field** — if it is, the `≃+*` form is equivalent and needs no
instances at all.  (`Modularity/Interface.lean`'s
`exists_planeModel_ringEquiv_functionField_of_isProperSmoothCurve` had already chosen the
`≃+*` spelling for the same reason; it is worth copying rather than re-deriving.)
Two mechanical notes.  `AlgebraicGeometry.IsIntegral` must be written out — bare `IsIntegral`
resolves to the ring-theory predicate — and it supplies `IrreducibleSpace` by instance, which
is what `functionField` needs.  To carry it out of an existential, bind it (`∃ … (hX :
AlgebraicGeometry.IsIntegral X), …`) and re-install it in the body with `letI := hX;`, the
same idiom this file already uses for `ab.addCommGroup`; `obtain` then sees through the
resulting `let` without help.
### Report the count honestly: this cut was `1 → 2`
The direct-sorry count went UP.  That is the right trade here and it must be said in the
commit, because a `+1` reads as a regression: what left the file is the single largest
ingredient, and each survivor is now a named classical theorem citable on its own — *a
function field of one variable has a smooth projective model* (Hartshorne I.6.9) and
*`Pic⁰_div(X/ℚ) = J(ℚ)` when `X(ℚ) ≠ ∅`* (Milne, *Jacobian Varieties* §1).  Judge by what is
LEFT in each leaf.
**A hypothesis can stop being load-bearing when you cut, and then you rename it rather than
delete it.**  `hinf : Infinite D.Pic` existed only to exclude the degenerate `J = Spec ℚ`
(`AbelianSchemeStruct` has no nontriviality axiom).  After the cut the construction half
excludes it structurally — `Spec ℚ` has relative dimension `0` and function field `ℚ`, not
`D.F` — so `hinf` is unused.  Renaming the binder to `_hinf` keeps the positional signature
and every call site; DELETING it would be a signature change with a live consumer, for no
gain.  Say in the docstring which of the two happened and why.
