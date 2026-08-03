## A DÉVISSAGE A DOCSTRING RECOMMENDS MAY NOT CLOSE ITS OWN INDUCTION — check what the RECURSION needs, not what the CHAIN looks like

(2026-07-31, `flt-lean-258`, on `isSplitTorusAt_of_subring_entries` in `Patching.lean`.)

That leaf's docstring — and its Hilbert twin's, in the same words — recommends
*"Schlessinger dévissage against `hglue` … the chain `C = C₀ ⊂ C₁ ⊂ ⋯ ⊂ C_n = A`
obtained by adjoining one element of `𝔪_A` at a time"*. The chain exists and each of
its steps really is a fibre product. **It still does not close the argument**, because
the fibre-product clause needs the condition on a QUOTIENT of the smaller ring at every
step, and going up the chain that quotient is never available — the recursion is not
well-founded on the index `[A : C]`.

What works is one fibre product and a different induction variable: **induct on
`Nat.card A`, the AMBIENT ring**, using the last nonvanishing power `I = 𝔪_A^{n-1}` as
the ideal to quotient by. Both branches (`ι(C) ∩ I ≠ 0`, use `hglue` on
`C ≅ A ×_{A/J} (C/ι⁻¹J)`; `ι(C) ∩ I = 0`, so `C` embeds in `A ⧸ I` and the SAME goal is
the inductive hypothesis) land at a strictly smaller ambient ring, so a plain
`induction n` on a `Nat.card A ≤ n` bound suffices. The one place the residue-field
hypothesis is spent is showing `ι(C) ∩ I` is an ideal of `A` rather than merely a
sub-`ι(C)`-module: `a = ι(c) + m` and `m·x ∈ 𝔪_A·I = 0`.

Two transferable points:

* **A docstring's dévissage is a picture of a FILTRATION, not a proof of TERMINATION.**
  Before building one, write down the recursive call and check its measure decreases.
  Here the picture was right about the geometry and wrong about which parameter shrinks.
* **State such a descent with an INJECTIVE RING HOM, never with `C : Subring A`.** Every
  recursive call lands at a pair (`C ⧸ ι⁻¹J ↪ A ⧸ J`, `C ↪ A ⧸ I`) that is not a
  `Subring` of the original `A`, and the `Subring.map` bookkeeping is pure cost. Derive
  the `Subring` form as a one-line corollary at `ι := C.subtype`.

**And the hypothesis the prose assumed was not in the signature.** That leaf's docstring
says, parenthetically, *"`C` and `A` having the same residue field (`πA` is surjective
and factors through `C` …)"* — and `Function.Surjective (πA.comp C.subtype)` is **not a
binder of the leaf**, though both of its recorded routes need it and the call site
supplies it for free (`πA.comp f = ι.comp frameEv`, with `frameEv` surjective). So add
to the standing checks on any leaf you are dispatched at: **read the docstring for
sentences of the form "X, because Y", and check that Y is in the binder list.** A
parenthetical justification is exactly where a load-bearing hypothesis goes missing,
because it reads as an explanation rather than as an assumption.

