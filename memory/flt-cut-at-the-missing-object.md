---
name: flt-cut-at-the-missing-object
description: When a leaf's classical proof runs through an object the tree lacks, cut AT that object — the rest is usually bookkeeping the file already owns
metadata:
  type: project
---

A leaf whose docstring says "needs the quotient abelian variety / Poincaré
reducibility / theory X, absent from tree, pin and `~/cs/FLT`" reads as
un-decomposable. It usually is not. **State the missing object's EXISTENCE with
exactly the properties the classical argument consumes, and the whole remainder
of the argument turns out to be already-proven bookkeeping.**

Measured on `range_eq_univ_of_abelianSubscheme_torsion_finiteBase`
(`Modularity/TateModule.lean`, 2026-07-31). Its recorded blocker was the
quotient `C = A'/B`. Cutting at `C` — one leaf giving `C`, its `𝒪_D`-action,
its kernel, its surjectivity on geometric points and one nonzero point; a
second leaf giving `C ≠ 0 ⟹ C[I] ≠ 0` — left an assembly of ~100 lines that
uses **no new input at all**: `exists_nsmul_eq_geomFibrePt` for divisibility of
`B(k̄)`, `exists_pow_mul_not_le_of_isMaximal` for `(q) = Iᵛ·J`, and the
partition of unity `1 = e + j` to project onto the `I`-primary part one element
at a time. The sketch's "the sequence of Tate modules is exact" was never
formed; the element-wise version needed nothing.

**Why:** the classical write-up names the objects it finds conceptually
convenient (Tate modules, exact sequences), not the objects the proof needs.
Those are two different lists, and only the second has to exist in Lean.

**How to apply:** before reporting a leaf as blocked on absent theory, write the
blocked object as a `sorry`ed existential with the conjuncts the argument
actually uses, and try to finish the proof over it in a scratch. If it goes
through, you have converted one unownable leaf into two standard named theorems
plus a machine-checked argument — and the two are separately dispatchable.
Check faithfulness of the new leaf the usual way: what degenerate witness
(`C = Spec k`, `π = 0`) discharges it, and which conjunct rules that out.

See [[flt-scratch-may-import-the-giant-file]] for the loop that makes this cheap,
and [[flt-cleaner-statement-harder-proof]] for choosing WHERE to cut.
