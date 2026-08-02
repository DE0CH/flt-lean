---
name: flt-assumption-in-a-docstring-is-an-unowned-leaf
description: "A docstring calling something \"the assumption on which these leaves rest\" is naming an unowned input; if two leaves rest on it, it is owed twice, and naming it de-duplicates the obligation at zero count."
metadata: 
  node_type: memory
  type: project
  originSessionId: 3f710d34-7ad7-46d2-a5b0-d50299b70398
  modified: 2026-08-02T11:49:46.800Z
---

(2026-08-02, `flt-lean-314`, `ModularCurve/X0.lean`'s integral-model cluster.)
A subsection comment ended: *"**That uniqueness argument is the assumption on
which the two geometry leaves rest**; it is not formalised here, and the check
that would refute it is …"*. That sentence is not a caveat — it is a LEAF with
no name, no owner and no `sorry`, and while it stayed unnamed each of the two
leaves resting on it was **strictly harder than the citation it advertised**:
Igusa / Deligne–Rapoport prove smoothness of the model THEY construct, so a
prover of "every model is smooth" owed the citation *and* the uniqueness — and
the uniqueness was owed TWICE, once inside each leaf, shared by nothing.

**The check**: grep leaf docstrings for `is the assumption`, `is not formalised`,
`rests on`, `we may assume`, `up to isomorphism` — each hit is a candidate for a
named leaf. Then ask whether more than one leaf cites it; if so, naming it is a
strict deduplication of obligation even when the count does not move.

**The repair that keeps the cheap half alive.** The natural fix — state the
citation as a bare existential ("SOME model is smooth") — SUBSUMES the
construction leaf and kills it (free-floating). Give the citation leaf the
construction leaf's OUTPUT as a hypothesis instead:

    theorem exists_smooth_connected_of_isX0NormalProperModel … (_M : IsX0NormalProperModel …) :
        ∃ XZ' xstr' jZ', ∃ _ : IsX0NormalProperModel N xstr' ystr jZ', Smooth… ∧ Connected…

`_M` is never used by the intended proof, and that is fine — it keeps the soft
construction CONSUMED and separately dispatchable
([[flt-discharged-hypothesis-defeats-floating]]). Hold the shared object
(`ystr`) FIXED across the conclusion, or the uniqueness leaf has to compare two
coarse spaces as well.

Accounting was `3 → 3` open leaves plus two proven declarations; say that
plainly. What changed is that no leaf hides an obligation and the three
survivors are each lookup-able.

**Falsity audit found on the way, and it is the shape to expect**: uniqueness of
normal proper models is FALSE at the degenerate level. At `N = 0` the coarse
space is empty, so `finite_compl` degenerates to "the model is a finite set",
and both `Spec ℤ_(ℓ)` (identity, proper) and `Spec 𝔽_ℓ` (closed immersion,
proper) satisfy every field — integral, integrally closed stalks, empty open
immersed, finite complement — while not being isomorphic. `0 < N` is
load-bearing for TRUTH.

Two Lean facts, both measured: `SmoothOfRelativeDimension 1` transports along an
iso over the base in three instance steps (an iso is an open immersion hence
`SmoothOfRelativeDimension 0`, and the comp instance adds, `0 + 1` reducing
definitionally). `GeometricallyConnected` does NOT — `GeometricallyConnected.comp`
needs `GeometricallyConnected e.hom`, which has no instance — use
`MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyConnected)`,
available because it is `IsStableUnderBaseChange`.

Related: [[flt-every-vs-some-representing-object]],
[[flt-a-leaf-can-contain-a-leaf]], [[flt-cut-docstring-states-the-rule-it-breaks]].
