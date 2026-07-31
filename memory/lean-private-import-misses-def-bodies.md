---
name: lean-private-import-misses-def-bodies
description: "A non-public `import` reaches THEOREM proof bodies but NOT `def` bodies under `@[expose] public section` — so a privately-imported constant can be used to prove a lemma and still be unusable to build the `Equiv` that lemma serves"
metadata:
  node_type: memory
  type: reference
---

`X0.lean` records that its `import Fermat.FLT.ModularCurve.EllipticScheme` is
NON-public **on purpose** — a `public import` propagates the reserved token `over`
through the whole cone and silently truncates a structure with a field of that name —
and that "everything from `EllipticScheme` stays inside its proof body, which is
exactly where the non-public import does reach".

That last clause is true and INCOMPLETE, and the gap cost a build cycle on
2026-07-31. Every project file opens with `@[expose] public section`, which exposes
**`def` bodies**. A `def` whose body mentions a privately-imported constant fails with
plain `Unknown identifier` — the same message a genuinely missing declaration gives,
and the same message you get for a *signature*, so it reads as "the import did not
work" rather than "the import worked and this is the wrong kind of declaration".

Observed in `X1.lean` with a private `import Fermat.FLT.ModularCurve.EllipticScheme`:

* `#check @Fermat.OnAffineWeierstrass` — **fine** (a command, not a declaration);
* `theorem foo : OnAffineWeierstrass … ` — fails, it is in a signature (expected);
* `noncomputable def bar := … coordinateRingEvalHom …` — **fails**, and this is the
  one that is not documented anywhere.

**How to apply.** Before planning a proof around a privately-imported API, ask whether
you need it in a `def` (an `Equiv`, a bundled hom, anything with computational
content) or only in a `theorem`. If a `def`, the private import buys you nothing and
there are three options, in order of preference:

1. restate the handful of lemmas you need locally, specialised — often the
   specialisation deletes half of them (specialising a functor-of-points dictionary to
   `C = K` replaced a bespoke `OnAffineWeierstrass` predicate with mathlib's own
   `WeierstrassCurve.Affine.Equation`);
2. add a re-export in the module that CAN see it, written entirely in that module's
   vocabulary — the pattern `X0.lean` already uses for
   `exists_weierstrassModel_geomFibreAddEquiv_of_ellipticScheme`;
3. make the import public — but only after checking what `open scoped` / reserved
   tokens it drags in. For `EllipticScheme` this is the option that is known-bad.

Related: [[flt-no-private-shielded-floating]].
