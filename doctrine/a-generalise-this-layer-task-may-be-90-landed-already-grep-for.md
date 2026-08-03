## A "GENERALISE THIS LAYER" TASK MAY BE 90% LANDED ALREADY — GREP FOR THE `_field`/`OverField` TWIN BEFORE READING THE `ℚ` ONE
(2026-08-02, `flt-lean-51`, on the `Rat → arbitrary field` generalisation of the
projective-Weierstrass elliptic scheme layer.)  The task prompt described the target
as `structure ProjGroupLaw (E : WeierstrassCurve Rat)` and set the job as "re-state it
over `{K : Type} [Field K]` and check what in its proofs used `Rat`".  It had been
`{F : Type u} [Field F]` **since two days before the prompt was written**, and so had
`isProper_projToSpec_field`, `smoothOfRelativeDimension_projToSpec_field`,
`geometricallyConnected_projToSpec_field` and
`ProjGroupLaw.toAbelianSchemeStructField`.  The entire scaffolding was in place; what
was missing was ONE assembly theorem, which took twenty lines and closed nothing.
**This is the ordinary state of a generalisation task in this tree, not an accident.**
A layer gets generalised in slices by successive agents, each landing the piece its
own leaf needed, and the prompt is generated from a snapshot of the `ℚ` declarations —
which are deliberately KEPT, so they still read exactly as they did before the
generalisation began.  A prompt describing the pre-generalisation state is therefore
consistent with the generalisation being nearly finished.
**The check is one grep and it must come before you read anything:**
    grep -nE '^(noncomputable )?(theorem|def|structure) .*(_field|OverField)' <the file>
then attribute the `sorry`s, because the surviving open leaves are the real task.  Here
that returned 23 `_field` declarations of which exactly TWO were open, and the honest
job was the assembly plus a precise measurement of the residue — not a port.
### Corollary 1: TWO INCOMPARABLE MODULES CAN CARRY RIVAL GENERALISATIONS OF ONE CONSTRUCTION
`ModularCurve/EllipticScheme.lean` and `Modularity/MoretBailly.lean` each carry a
complete general-field development of the same object — `ProjGroupLaw` +
`toAbelianSchemeStructField` + an open `m`-existence leaf on one side,
`ProjGroupLawOverField` + `toAbelianSchemeStruct` + `ofMul` +
`exists_projMulOverField_geomFibreAddEquiv` on the other.  Measured: their import
closures are **58 and 176 modules and are INCOMPARABLE**, and both import
`ProjectiveModelOverField.lean`, the common ancestor where the shared `m`-existence
belongs.  Neither file can see the other, so neither author could have known.
**No ownership or frontier instrument sees this**: the two leaves have different
names, different statements (one publishes `F`-rational points, the other
`F̄`-geometric points with Galois equivariance), and both are honestly open.  Only an
import-closure computation plus a short-name intersection finds it.  Compute the
closure with an assertion that every visited file EXISTS — a swallowed
`FileNotFoundError` truncates the walk and manufactures exactly the "incomparable"
answer you were hoping for.
### Corollary 2: A PORT ESTIMATE GOES STALE BY WHATEVER HAS SINCE BEEN PORTED INTO THE COMMON ANCESTOR
`EllipticScheme.lean`'s own docstring priced the remaining `ℚ → F` port of the group
law at **6677 lines, 611 comment-stripped `ℚ` occurrences**, quoting a sibling's
measurement.  Intersecting the chain's declaration names with
`ProjectiveModelOverField.lean`'s shows **39 of the 122 chain declarations — the whole
smoothness/chart block, a contiguous 1160-line run — are ALREADY PORTED over an
arbitrary field, in a module `EllipticScheme.lean` IMPORTS.**  They include every one
of the heaviest declarations by `ℚ`-count (`isStandardSmoothOfRelativeDimension_`
`projChartAway` 24, `false_of_eval_pderiv_projPolynomial_eq_zero` 21,
`projChart_jacobian_span_eq_top` 14).  The `ℚ` copies still sitting in
`EllipticScheme.lean` are now redundant duplicates of already-general theorems.
So the measurement to run before costing any port, and it is ten lines of Python:
    chain   := declarations of the ℚ chain, comment-stripped
    ported  := short names declared in the general-base module you already import
    residue := chain − ported          # THIS is the port, not `chain`
What survived here is the GLUING half (`IsProjMulOn`, the cover machinery,
`exists_projMulOfCoords`, `exists_projMul`, associativity, `nonempty_projGroupLaw`)
and the **53 `hom_ext_spec_rat` sites**, against only 7 `Subsingleton` and 1
`base_eq` — i.e. one shortcut used 53 times, which is the shape the standing
"PORT THE SHORTCUT, NOT ITS CALL SITES" rule is about, and its replacement
(`fromOfGlobalSections_comp_projToSpec`) is already proven in the ancestor module.
### Corollary 3: DERIVING A WEAKER STATEMENT FROM A BUNDLED LEAF IS NOT THE SPLIT ITS DOCSTRING FORBIDS
`exists_projGroupLaw_relPointAddEquiv_field` is `∃ gl : ProjGroupLaw E, <dictionary>`,
and its docstring forbids splitting it — correctly: `ProjGroupLaw` pins nothing about
`m`, so the `∀ gl, <dictionary>` half is FALSE (translate the zero section).  That
prohibition does **not** block deriving `Nonempty (ProjGroupLaw E)` from it, which is
a weakening in the derivable direction and introduces no `∀ gl` anywhere.  Read such a
prohibition for the DIRECTION it forbids; `∃ x, P x → ∃ x, True` is never the
falsity-of-cut being warned about.
Rider: taking that route makes every consumer inherit the bundled leaf's extra
conjunct.  Cutting the weaker existence as its own leaf instead would be a DUPLICATE
CUT of one construction — both halves come from the same Bosma–Lenstra gluing — so the
frontier would rise while no obligation got smaller.  Prefer the over-dependency,
and write into the docstring what would justify splitting later.
