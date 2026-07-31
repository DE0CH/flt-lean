---
name: lean-private-import-suffices-for-proof-bodies
description: A PRIVATE `import` does make a module's names usable inside theorem PROOFS; only names occurring in a statement (or an exposed def body) need a `public import` — a widely-repeated claim to the contrary is false
metadata:
  type: reference
---

Under Lean's module system, `import M` (no `public`) makes `M`'s declarations
available for elaboration in the importing module; it only stops them being
RE-EXPORTED to that module's own importers. Since **theorem proof bodies are
elided**, a `public theorem` may freely use privately-imported constants in its
proof. What needs a `public import` is a name occurring in a **statement**, or
in the body of a `def`/`abbrev`/`instance` that `@[expose]` publishes.

**Measured 2026-07-31** while cutting
`exists_local_hopf_tensor_etale_algEquiv_of_finite_hopf`
(`Fermat/FLT/GaloisRepresentation/HardlyRamified/ModThree.lean`). Its docstring
said, and had said since 2026-07-28:

> Whoever takes this leaf must add `public import Fermat.FLT.GroupScheme.ConnectedEtale`
> — a transitively-reached or private import does not make the names available
> even in proof bodies.

Both halves were wrong. `ModThree` had carried a **private**
`import Fermat.FLT.GroupScheme.ConnectedEtale` all along (added for
`exists_connected_counit_idempotent_at_three`), and a 300-line block of new
public theorems whose proofs call
`Bialgebra.exists_connected_counit_idempotent` elaborates against exactly that
configuration under `@[expose] public section`, `EXIT=0`, no warnings. The only
edge that had to be `public` was `Mathlib.RingTheory.HopfAlgebra.Quotient`,
because `Ideal.IsHopfIdeal` occurs in two of the new STATEMENTS.

**Why it matters beyond bookkeeping:** the claim was load-bearing in a dispatch
sense. It made a leaf look as though it required editing the header of a
71 000-line module — a change that widens the export surface of a file four
other modules import, and therefore a change an agent will hesitate over or
route past. The true cost was four mathlib import lines.

**How to apply:** before promoting an import to `public` to reach a name, check
where the name actually occurs. Statement or exposed body → `public`. Proof
body only → the private import you probably already have is enough. And check
the header first: this project's big modules already import far more than their
`public` block suggests. The test is one `lake env lean` on a scratch module
that mirrors the target's import lines — about 10 seconds.

Related: [[lean-module-system-elides-proof-bodies]] (the same elision, seen from
the other side: it is why an imported theorem's `value?` is `none`), and
[[flt-verify-in-a-scratch-module]] if that exists.
