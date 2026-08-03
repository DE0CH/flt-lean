## AN "IRREDUCIBLE ALONG AXIS X" VERDICT CAN BE SEARCHING FOR THE OBJECT WHILE THE CITATION IS ALREADY IN THE FILE
(Same task, and it is what closed the leaf.) `nonempty_gamma0AtlasOver_specLoc` — the
Katz–Mazur atlas of `Y_0(N)` over `ℤ_(ℓ)` — carried a dated, re-checked, entirely correct
verdict: *`ModularCurve` is absent from mathlib entirely, there is no `DeligneRapoport`
or integral model of a modular curve in mathlib, `~/cs/FLT` or this project; the check
that refutes it is to produce the `Γ₀(N)`-atlas over `ℤ[1/n]`*. Every clause was true.
The leaf closed with no atlas produced and no new leaf opened.
What it missed is that a **fusion one day earlier had already replaced the two
base-specific representability leaves by base-general ones** —
`exists_rigidifiedModuliSchemeData_of_isUnit` and
`isAffine_rigidifiedModuliSchemeData_of_isUnit`, stated over an arbitrary ring `R` with
`3 ≤ n`, `IsUnit (n : R)`, `IsUnit (N : R)`. Those hypotheses ARE Katz–Mazur's own
proviso, which is exactly what the leaf's `hu` already carried. Everything between them
and the atlas was already stated over an arbitrary base and PROVEN. So the
mixed-characteristic base was never the obstruction the verdict named; nobody had read
the `𝔽_ℓ` route at a base that is not a field.
Two things generalise:
* **A verdict names an AXIS, and the axis is the author's search, not a property of the
  statement.** This one searched for *an atlas over a base of mixed characteristic*. The
  refuting check it prescribed was to build that object — so following the docstring's own
  advice would have cost a theory build. Ask instead which CITATION the leaf needs and
  whether some sibling has already been generalised to cover it; in a tree that fuses
  base-specific leaves as aggressively as this one, that happens on a timescale of days.
* **A base-specific chain transcribes to a general base exactly when the base is spent
  through a NUMERICAL condition.** Here the whole `𝔽_ℓ` torsion/Isom chain spends `𝔽_ℓ`
  twice — the fibrewise `ℤ/n`-basis of `E[n]`, and étaleness of `E[n] ⟶ T` — and both go
  through `(n : K) ≠ 0` at the geometric points, which is what
  `WeierstrassCurve.n_torsion_dimension` and `etale_nTorsion_of_natCast_ne_zero` actually
  ask for. `¬ ℓ ∣ n` was only the route to it. Over `ℤ_(ℓ)` no single characteristic
  exists, so the `CharP` form is unavailable and the `(n : K) ≠ 0` form is the only one
  that survives — which is the tell that it was the real hypothesis all along. The note on
  `exists_isomTorsor_of_geomPoint_specF` said so in as many words and nobody had taken it
  at its word.
Corollary, and it is the cheap check: **before believing a base-specific chain must be
rebuilt, grep the base hypothesis through it and see what each use extracts.** If every
use extracts the same numerical fact, the chain is already general and the transcription
is mechanical.
