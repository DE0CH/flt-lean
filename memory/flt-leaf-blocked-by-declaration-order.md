---
name: flt-leaf-blocked-by-declaration-order
description: A leaf can be unprovable in place while the machinery for it sits 10k lines lower in the SAME file; compare line numbers before reporting "no route"
metadata:
  type: project
---

`realCoeff_norm_le_of_isWeightTwoEigenform` (`X0.lean:~39715`, Ramanujan–Petersson in
weight two) was twice audited as having NO route. Read in place that is correct — nothing
above it mentions a Frobenius. But the same file carries `IsWeilEigenvalues`,
`IsEichlerShimuraTransform`, `isEichlerShimuraTransform_x0` and
`exists_x0Compactification_finiteField` at lines 49104–50700: every ingredient of the
classical proof except PURITY (`‖z‖ = √ℓ` for the nonzero Frobenius eigenvalues, i.e. the
Riemann hypothesis for curves). Lean is strictly ordered, so the leaf cannot cite them.

**Why:** an 81 000-line module generates this blocker by itself, and it is invisible to
every instrument — the leaf looks ordinary, the machinery looks present, and both readings
are true. Neither block can move (the analytic cluster has consumers at ~41 200; the
geometric one rests on most of 41 000–49 000), so the real remaining work is a MODULE
SPLIT, not the mathematics an audit would name.

**How to apply:** when auditing a leaf, `grep -n` the machinery IN THE LEAF'S OWN FILE and
check the line number is smaller. Report "blocked by order" rather than "Deligne is
missing", which sends a worker at a subtree that is already three quarters written. And
search absences by the object THIS TREE builds, not the one the literature names — the
2026-07-28 audit searched for `A_f` (the abelian variety of the FORM) and so missed the
Jacobian of the modular curve, which is where Eichler–Shimura lives here.

Dividend of the same reading: a conjunction of "different mathematics" is worth re-testing
for one clause implying the other. Reality of `a_p` was believed to need Petersson
self-adjointness; purity gives `αβ = p` with `‖α‖ = √p`, hence `β = conj α` and
`a_p = 2 Re α` real for free — a whole subtree deleted. See
[[flt-two-leaves-may-be-one]] and [[flt-reduce-to-an-open-leaf-not-a-proof]].
