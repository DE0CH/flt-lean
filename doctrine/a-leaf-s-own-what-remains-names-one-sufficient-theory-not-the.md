## A LEAF'S OWN "WHAT REMAINS" NAMES ONE SUFFICIENT THEORY, NOT THE CHEAPEST ONE

(2026-07-31, flt-lean-107. Closed two direct leaves that had each been audited as atomic.)

`galoisConj_cmEndomorphism` in `X0.lean` — the `Γ_ℚ`-action on `End(E_ℚ̄)` is `Gal(K/ℚ)` —
carried a careful sketch routing it through *`End(E)` is commutative in characteristic `0`,
because quaternionic CM occurs only in characteristic `q > 0`*. True, deep, and nowhere in
this tree; that is why the node read as atomic CM theory for three days.

The proof needs no CM theory at all. `λ(φ)`, the scalar an isogeny acts on the invariant
differential by, is a ring map `End(E_ℚ̄) → ℚ̄` that is INJECTIVE in characteristic `0` and
Galois-equivariant — and injectivity into a *field* subsumes the commutativity the sketch
wanted, for free. Then `c := λ(φ)` satisfies `φ`'s own quadratic, `σ c` satisfies it too,
a quadratic has two roots, and injectivity turns each root into an identity of maps. About
sixty lines.

Three transferable rules, in order of how much they cost to skip:

* **A "MISSING MACHINERY" paragraph is evidence about the axis its author searched, and
  nothing more.** It is written *before* anyone tries, so it names the first sufficient
  route that came to mind. Ask what OTHER invariant separates the two cases — here, the
  question "what distinguishes `φ` from `1 − φ`?" has an answer that is a *number*, and any
  faithful numerical invariant would have done.
* **The sibling argument may already be written, in a file that IMPORTS yours.**
  `MazurTorsion.lean` (downstream of `X0.lean`) had `exists_sqrtNegOne_galSign`: the same
  three moves — `exists_isDiffChar`, `isDiffChar_galConj`, `eq_of_isDiffChar` — for
  `Ψ² = [−49]`. This extends `[[flt-missing-machinery-may-be-downstream]]`: the downstream
  sibling is not necessarily something to HOIST. Here it pointed at a third module
  (`EllipticCurve/DifferentialCharacter.lean`) that was upstream-compatible all along, and
  the whole fix was one `public import` in `X0.lean`. **"Not available here" often means
  "not imported here".** Check the import direction before concluding a theory is missing —
  and grep the whole tree, not your own module's cone.
* **A helper you need may exist only DOWNSTREAM, and then you copy it, deliberately.**
  `MazurTorsion.exists_rat_of_galois_fixed` (Galois descent for scalars, three lines under
  `set_option backward.isDefEq.respectTransparency false` because `IsGalois ℚ ℚ̄` does not
  synthesize at this pin) could not be used from upstream. Duplicating it under a different
  name with a docstring saying which copy should survive is right; renaming or moving the
  downstream one mid-task is a signature change with call sites you did not audit.

And the accounting note, because it is the shape that makes this worth writing down: the
leaf under attack was `exists_isogenyCurve_classNumberOne` in `MazurTorsion.lean`, and the
first working route closed it by opening a strictly stronger leaf UPSTREAM (net −1). Only
then did the upstream leaf turn out to be provable outright (net −2). **A cut that moves a
leaf upstream is worth banking even when you cannot close it** — it puts the residue where
the machinery lives, which is exactly where the next attempt can see it.

