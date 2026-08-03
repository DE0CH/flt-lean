## AN EXPRESSIBILITY CUT MOVES NO COUNTER AND IS STILL THE WHOLE STEP

(2026-07-31, `flt-lean-204`, on `nonempty_modularTateCarrierData_of_jacobian`.)

Some leaves are not hard, they are **unsayable**. The Eichler–Shimura leaf's own docstring
had diagnosed itself correctly: it was ATOMIC "and it is a statement about EXPRESSIBILITY,
not about difficulty" — the `p`-adic Tate module of `J₀(M)` could not be *written down* in
Lean, because `Fermat.TatePt` takes a `Mult ab R` argument and no `m : Mult ab 𝒪_ℚ` existed.
Every split anyone could state therefore had to quantify over an ABSTRACT carrier of the
right dimension, and such a split manufactures a FALSE leaf (Eichler–Shimura is false for an
arbitrary faithful Hecke module of the right dimension).

The cut that unblocks it adds the missing datum as a HYPOTHESIS and discharges it in glue:

    theorem X_of_mult … (m : Mult ab 𝒪_ℚ) : C := sorry      -- the leaf, now sayable
    theorem X … : C := by obtain ⟨m⟩ := nonempty_mult_ringOfIntegersRat ab; exact X_of_mult … m

Here `Mult ab 𝒪_ℚ` is free — `Rat.ringOfIntegersEquiv : 𝒪_ℚ ≃+* ℤ` and every abelian group is
a `ℤ`-module, so `act a y := (Rat.ringOfIntegersEquiv a) • y` and the six axioms are the
`zsmul` laws plus `map_zsmul` on the additive map `RelPoint.pre`. Fifty lines, first try.

**Two things to carry forward.**

- **The sorry count does not move**, and neither does the transitive count: one leaf in, one
  leaf out, plus a proven construction. To `flt-frontier.py` and to the `declaration uses
  'sorry'` warning set this cycle produced *nothing*. It produced the only step that made the
  next four possible. So do not judge a cycle by the delta, and do not let a leaf sit because
  the work under it "would not close anything".
- **The tell is in the leaf's own docstring**, and it is a phrase, not a feeling: a leaf that
  says a split "cannot be stated", "would manufacture a false leaf", or "the object does not
  exist yet" is an expressibility leaf, and the task is to BUILD THE OBJECT, not to attack the
  mathematics. Read the docstring for that phrase before costing the leaf as hard.

Corollary for whoever writes the construction: **it must land with its consumer in the same
commit**, since a free-floating definition is not allowed here — which is why the restatement
and the construction are one edit and not two.

