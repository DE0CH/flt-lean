---
name: flt-route-reaches-across-modules-unnecessarily
description: "When a route names a lemma from another module for one step, check whether the module supplying the rest of the API already has a cheaper primitive"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 166e8e6c-8a45-4e72-85eb-6e2740a0c969
  modified: 2026-08-02T03:47:51.783Z
---

A leaf's recorded route is written step by step, and each step is priced against
whatever the author happened to recall. When four of five steps cite one module
and ONE step reaches into a different one, that odd step is the one to re-price
first — the module already carrying the API usually has a cheaper primitive for
it, because it needed the same fact for its own proofs.

**Measured on `exists_dualIsogeny_of_isIsogeny` (`MazurTorsion.lean`, 2026-08-02).**
Steps 2–6 cite `Fermat/FLT/EllipticCurve/Isogeny.lean` (`Isogeny.dual`,
`dualHom_comp`, `degree_of_ne_zero`). Step 1 — *`φ ≠ 0`* — reached across to
`Fermat/FLT/EllipticCurve/Torsion.lean` for `n_torsion_dimension`, proposing to
contradict `#E(ℚ̄) = N` with `E[N+1] ≃+ (ZMod (N+1))²`. That route works but drags
in `nTorsion`, whose carrier is the DOUBLE base change `((E⁄K)⁄K).Point`, plus a
`[DecidableEq k]` binder and a subgroup-cardinality argument.

`Isogeny.lean` has both halves outright, in the generality already in scope:

* `nsmul_surjective [IsAlgClosed F] [W.IsElliptic] (hn : n ≠ 0)` — multiplication
  by `n` is ONTO, so a group killed by `n` is trivial;
* `exists_point_veluPointX_eq [IsAlgClosed F] [W.IsElliptic] (t : F)` — a NONZERO
  point over every `x`-coordinate, i.e. nontriviality.

Five lines, no `CharZero`, no torsion count, no second module. **The whole leaf then
closed as pure assembly, axiom-clean, with no new leaf.**

**The check, and it is one `grep` of the module you are already using:** before
following a route's cross-module step, grep that module's own declaration list for
the *property* the step needs (here: surjectivity of `[n]`, existence of a point) —
not for the lemma name the route gave you. A module that proves a dual-isogeny API
necessarily already owns divisibility and point-existence; those are its inputs.

Same family as [[flt-leaf-cost-estimates-are-hypotheses]] and
[[flt-inventory-audits-understate-what-exists]], with a cheap syntactic tell: the
step whose citation names a *different file* from its neighbours.
