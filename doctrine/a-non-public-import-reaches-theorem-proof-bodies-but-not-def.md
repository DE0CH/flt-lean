## A NON-PUBLIC `import` REACHES THEOREM PROOF BODIES BUT NOT `def` BODIES

(2026-07-31, cost one build cycle.) `X0.lean` records that its
`import Fermat.FLT.ModularCurve.EllipticScheme` is non-public **on purpose** — a
`public import` propagates the reserved token `over` through the whole cone and
silently truncates a structure with a field of that name — and that "everything from
`EllipticScheme` stays inside its proof body, which is exactly where the non-public
import does reach". That clause is true and INCOMPLETE.

Every file here opens with `@[expose] public section`, which exposes **`def` bodies**.
So a `def` whose body names a privately-imported constant fails with a bare
`Unknown identifier` — the *same* message a missing declaration gives and the same one
a signature gives, so it reads as "the private import does not work at all" rather
than "it works, and this is the wrong kind of declaration". Measured in `X1.lean`:
`#check @Fermat.OnAffineWeierstrass` fine (a command); the name in a theorem SIGNATURE
fails (expected); the name in a `noncomputable def` body fails (not documented
anywhere).

So before planning a proof around a privately-imported API, ask whether you need it in
a `def` — an `Equiv`, a bundled hom, anything with computational content — or only in
a `theorem`. If a `def`, the private import buys nothing. Three ways out, best first:
**restate the few lemmas locally, specialised** (specialising a functor-of-points
dictionary to `C = K` deleted half of them, `OnAffineWeierstrass` giving way to
mathlib's own `WeierstrassCurve.Affine.Equation`); **add a re-export in the module that
can see it**, written in that module's vocabulary, which is the pattern `X0.lean`
already uses for `exists_weierstrassModel_geomFibreAddEquiv_of_ellipticScheme`; or make
the import public, which for `EllipticScheme` is known-bad.

