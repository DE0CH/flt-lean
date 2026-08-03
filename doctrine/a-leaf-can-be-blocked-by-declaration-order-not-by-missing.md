## A LEAF CAN BE BLOCKED BY DECLARATION ORDER, NOT BY MISSING MATHEMATICS
(2026-07-31, `realCoeff_norm_le_of_isWeightTwoEigenform`.) Two audits of the same leaf, both
careful, both correct, reached opposite verdicts — and the reason is a failure mode no rule here
covered. The leaf is Ramanujan–Petersson in weight two. Read IN PLACE, at `X0.lean:39715`, there is
no route: nothing above it mentions a Frobenius. Grepped ACROSS THE TREE, the machinery is
overwhelming: `IsWeilEigenvalues`, `IsEichlerShimuraTransform`, `isEichlerShimuraTransform_x0` and
`exists_x0Compactification_finiteField` — the Frobenius eigenvalues of `X_0(N)_{𝔽_ℓ}` paired over
the eigenvalues of `T_ℓ`, everything the classical proof needs but purity — **are in the same
file**, at lines 49104–50700. Ten thousand lines BELOW the leaf, and Lean is strictly ordered.
So the verdict "no route" was true of the position, not of the tree, and "the machinery exists" was
true of the tree, not of the position. **When auditing a leaf, compare LINE NUMBERS, not just
names**: `grep -n` the machinery in the leaf's own file and check it is above.
Two things follow, and they are what makes this worth a section rather than a footnote.
**An oversized module manufactures this class of blocker by itself.** In an 81 000-line file the
analytic cluster (~39 000) and the geometric cluster (~49 000) cannot see each other in one
direction, and neither block can move: the analytic one has its own consumers at ~41 200, the
geometric one rests on most of the 41 000–49 000 range. The repair is a MODULE SPLIT, which is
expensive and contended — but it is the honest name of the remaining work, and calling it "Deligne
is missing" instead sends workers at a subtree that is already three quarters written.
**An absence audit is only as good as the OBJECT it searches for.** The 2026-07-28 check on this
leaf concluded "no Frobenius and no purity anywhere in the tree" and it searched for `A_f`, the
abelian variety attached to the FORM. The file builds the Jacobian of the MODULAR CURVE, which is
where Eichler–Shimura actually lives here, so the search missed 1 200 lines of exactly the wanted
machinery sitting in the same module. Before reporting an absence, name the object the LITERATURE
would use and the object THIS TREE builds, and search for both.
And the mathematical dividend, which is the shape to look for when a leaf is a conjunction: the
clause the old docstring called "the half that is not Deligne" — reality of `a_p`, routed through
self-adjointness of `T_p` for the Petersson product, i.e. a whole second development — **is a
COROLLARY of the other half.** Purity gives `α β = p` with `‖α‖ = √p`, whence `β = conj α` and
`a_p = 2 Re α` is real for free (`exists_real_of_weilPair`, twelve lines). A conjunction of
"different mathematics" is worth re-testing for exactly this: one clause implying the other deletes
a subtree.
