## WHEN YOUR TARGET'S TWIN IS PROVEN, READ THE TWIN'S *PROOF* — AND TRANSPORT THE ARRANGEMENT, NOT THE STATEMENT
(2026-08-02, `flt-lean-95`, `exists_heckeCorrespondenceFamilyGamma1` in
`ModularCurve/X1.lean`.)  This development is built out of `Γ₀`/`Γ₁` twins, and the
standing advice about them is about DOCSTRINGS — a correction applied to one twin
does not propagate to the other.  There is a stronger and much cheaper move that
nothing above states, and it closed this leaf in one afternoon:
**When the twin is PROVEN, the useful thing is not its statement but the SHAPE OF
ITS PROOF.**  If the twin is proven over a SMALLER leaf, then your leaf is very
likely that smaller leaf BUNDLED WITH FORMAL GLUE, and the recut is a verbatim
transport rather than a piece of mathematics.
Here the `Γ₀` side had been arranged since 2026-07-30 as
    exists_heckeCorrespondenceMorphism   (leaf: a MORPHISM κ : X ⟶ J + the recipe)
    exists_heckeCorrespondenceFamily     (PROVEN over it, ~40 lines)
while the `Γ₁` side carried the FAMILY form as its leaf, bundling four
obligations — an assignment on points, its NATURALITY, the BASE-POINT clause, and
the RECIPE — of which three are formal.  Given `κ`, set `ε := post κ o`; then
`c g x := post κ x − pre g ε` with `e := −ε` satisfies naturality (one
`Category.assoc`), the base-point clause by construction, and the recipe (the
constant cancels).  **`X0.lean`'s proof transported character for character — not
one tactic changed — and compiled first try in a 4-second scratch.**
Three things make this worth reaching for by default:
* **The cheap check is a `grep` for the twin's name followed by reading its `by`
  block.**  Both files' docstrings said the two were "the same content"; only the
  proof body says over WHAT.  `X0.lean` even carried the instruction — *"a prover
  should start from `exists_heckeCorrespondenceMorphism`"* — and the `Γ₁` side had
  simply never been brought into line.  A twin that is proven is an ARRANGEMENT
  somebody already designed and debugged; inheriting it costs a `sed`.
* **Say out loud that the count does not move, and that the residue is a priori
  STRONGER.**  This was `1 → 1`, and the new leaf asks for a morphism of schemes
  where the old asked only for a natural family on points — recovering the former
  from the latter is not formal.  That is the right trade when the stronger form is
  the CLASSICAL statement (here: the Hecke correspondence trace really is a
  morphism `X_1(N) ⟶ J_1(N)`) and when a known future consumer needs it (the
  Atkin–Lehner commutation variant is built on the `Γ₀` morphism form, not the
  family form).  It is the wrong trade when the strengthening is towards something
  nobody has a route to — so name the classical theorem, or do not strengthen.
* **A falsity audit on the bundled form is EVIDENCE FOR the derived statement, not
  an obstacle to the recut, and it must be KEPT.**  The family form here is FALSE
  without an existentially bound constant `e` (`N = 11`, `ℓ = 2`: the `Γ₁`
  correspondence moves the rational cusps of `X_1(11)`, so `ε ≠ 0`).  The morphism
  form imposes no normalisation at the base point, so that witness is CONSISTENT
  with it and `ε` is simply the value `post κ o` the derivation reads off.  Check
  this explicitly before recutting — a residue that the twin's own witness refutes
  is the failure this move can produce — and then leave the audit where it is,
  under a paragraph saying the derivation SUPPLIES the constant rather than
  removing it.
**The receipt for a recut of this shape is two lines and belongs in the commit**,
because a `−1 +1` warning-set delta is indistinguishable from one closure plus one
unrelated disclosure:
    git diff -- <file> | grep -E '^[+-] *sorry *$'    # exactly one +, one −
    grep -cE '^\s*sorry\s*$' <file>                   # equal before and after
and attribute the compiler's warnings to declarations, so you can state that the
NEW name carries a sorry and the OLD one does not.
