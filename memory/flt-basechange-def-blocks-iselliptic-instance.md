---
name: flt-basechange-def-blocks-iselliptic-instance
description: "WeierstrassCurve.baseChange is a plain def, so mathlib's (W.map f).IsElliptic instance does not fire on E⁄K — supply it with inferInstanceAs"
metadata: 
  node_type: memory
  type: project
  originSessionId: 166e8e6c-8a45-4e72-85eb-6e2740a0c969
  modified: 2026-08-02T03:47:34.940Z
---

`WeierstrassCurve.baseChange` (mathlib, `EllipticCurve/Weierstrass.lean:236`) is a
plain `def`, **not** `abbrev`/`@[reducible]`:

```lean
def baseChange [Algebra R A] : WeierstrassCurve A := W.map <| algebraMap R A
scoped notation:max (priority := low) W:max "⁄" A:max => baseChange W A
```

Mathlib registers `instance : (W.map f).IsElliptic` (same file, ~:448), but instance
search will not unfold the `def`, so **`(E⁄K).IsElliptic` fails to synthesize** even
with `[E.IsElliptic]` in scope. Symptom, and it is the first line to break:

    failed to synthesize instance of type class
      WeierstrassCurve.IsElliptic E⁄(AlgebraicClosure ℚ)

Supply it by hand, once, at the top of the proof:

```lean
haveI : (E⁄(AlgebraicClosure ℚ)).IsElliptic :=
  inferInstanceAs ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).IsElliptic)
```

`Fermat/FLT/EllipticCurve/Isogeny.lean` uses exactly this idiom inside
`exists_point_veluPointX_eq` (`haveI : (W⁄F).IsElliptic := inferInstanceAs W.IsElliptic`),
so copy from there rather than re-deriving.

**Why it bites late rather than early.** `(E⁄K).Point`, `→+` between such
point groups, `AddSubgroup.zmultiples` and `(N : ℕ) • P` all elaborate *without*
`IsElliptic`, so a STATEMENT mentioning them compiles fine and the failure only
appears when the proof first names `Isogeny`, `Isogeny.degree` or `Isogeny.dual`.
A statement that elaborates is therefore no evidence the instance is available.

**Related trap in the same family:** writing `m • (0 : (E⁄K).Point)` with `m : ℤ`
freshly in a goal can fail with `failed to synthesize HSMul ℤ (E⁄K).Point ?m`, while
the *same* term arising from `AddSubgroup.mem_zmultiples_iff` is fine (the lemma's
own statement fixes the instance). Do not fight it — reach the conclusion through
orders instead: `addOrderOf_dvd_of_mem_zmultiples` then
`addOrderOf_dvd_iff_nsmul_eq_zero` (both `@[to_additive]` images of
`orderOf_dvd_of_mem_zpowers` / `orderOf_dvd_iff_pow_eq_one`) proves
`Pt ∈ zmultiples g → addOrderOf g = N → N • Pt = 0` with no `smul` juggling at all.

See [[flt-leaf-cost-estimates-are-hypotheses]] and
[[flt-route-residue-is-the-cheap-route]].
