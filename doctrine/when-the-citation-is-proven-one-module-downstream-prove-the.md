## WHEN THE CITATION IS PROVEN ONE MODULE DOWNSTREAM: PROVE THE ELEMENTARY HALF UPSTREAM AND RESTATE THE RESIDUE IN THE DOWNSTREAM VOCABULARY
(2026-08-02, `flt-lean-344`, `irrationalJ_of_selfNIsogenyPair_oneSixtyNine` in
`ModularCurve/X0.lean`.)  That leaf was priced at *"the theory of complex
multiplication — `End(E)` for a CM elliptic curve as an order in an imaginary
quadratic field, and the degree of the class polynomial.  **Absent from mathlib
as of this pin**: `grep -rn "classPolynomial\|HilbertClassPolynomial\|ringClassField"
.lake/packages/mathlib/` returns nothing."*  The grep is correct and it is the
wrong tree: the ENTIRE discriminant-`−676` apparatus is PROVEN in
`Fermat/FLT/FreyCurve/MazurTorsion.lean` — `classPoly676_of_endSq_neg169`
(the CM main theorem at `−676`, over the uniform leaf
`classNumberOne_of_end_closure_eq_top`), `classPoly676_no_rat_root`,
`not_exists_thirteen_mul_of_ker_order_169` — and that file `public import`s
`X0.lean`, so nothing there is nameable from the leaf.  This is the standing
"missing machinery may be DOWNSTREAM" trap with the absence claim scoped to
`.lake/packages/mathlib/`, which is where it becomes convincing.
**Finding it does not close the leaf, and hoisting four declarations plus their
cone out of a 47 000-line contended file is its own task.  What ONE run can do,
and what pays permanently, is three things:**
1. **Split off whatever half of the leaf is ELEMENTARY and prove it upstream.**
   `W.j ∉ ℚ` bundled the CM identification of `j` with *"the six roots of
   `H_{−676}` are irrational"*.  The second is the rational root theorem plus
   one congruence mod `5` — sixty lines, no elliptic curve in it, no class
   number — and it was already proven downstream, so it was copied upstream
   **under a different name** (`classPoly676_no_rat_root_x0`) with a docstring
   saying which copy should survive.  Deliberate duplication of a PROVEN,
   dependency-free helper is the recorded pattern, and two byte-identical
   proofs of one proposition cannot drift when the coefficient literal is
   quoted in full in both.
2. **Restate the residue so its conclusion is CHARACTER FOR CHARACTER the
   downstream theorem's.**  The new leaf
   `classPoly676_of_selfNIsogenyPair_oneSixtyNine` concludes "`W.j` is a root of
   this degree-`6` literal", which is exactly what `classPoly676_of_endSq_neg169`
   concludes.  When the hoist eventually lands, the leaf closes by ONE
   application rather than by a fresh development — and until it lands, the leaf
   is a statement a CM specialist can read without knowing this file.
3. **Write the downstream inventory into the leaf's own docstring, with the
   one-command refuting check** (`grep` the name in the downstream file, read
   whether its body is a `sorry`).  That is the artefact that stops the next
   three agents re-deriving "CM theory is missing".
**The count is `1 → 1` and must be reported that way.**  Judge it by what is
LEFT: the residue no longer mentions `Set.range (algebraMap ℚ ℚ̄)`, no longer
mentions rationality at all, and no longer bundles an elementary arithmetic fact
with a chapter of class field theory.
**The generalisable grep, and it is not the one the absence claim ran**: search
`Fermat/` for the CONCLUSION's shape.  Here the degree-`6` coefficient literal
is unmistakable and one `grep` for its leading coefficient finds the whole
downstream cluster; a search for "class polynomial" finds nothing, because the
development has no such notion and writes the polynomial out.
Two riders measured on the same run.  The assembly is **three tactic lines** —
`rintro ⟨x, hx⟩`, push the ring hom through the literal with
`simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]`, and appeal to
`(algebraMap ℚ (AlgebraicClosure ℚ)).injective` — so the elementary half really
was the whole of what the old statement added.  And the scratch loop against the
target's OWN stale olean is **7 seconds** here (`public import` the module being
edited; the stale olean has every name the new text refers to, which is exactly
why it works), against ~25 minutes for `lake build`; the entire recut was
developed in four such rounds and compiled first try.
