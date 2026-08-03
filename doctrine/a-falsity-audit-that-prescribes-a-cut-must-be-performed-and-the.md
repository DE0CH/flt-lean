## A FALSITY AUDIT THAT PRESCRIBES A CUT MUST BE *PERFORMED*, AND THE CHEAP WAY IS "SORRY THE LOWEST TRUE CONSUMER, DELETE THE FALSE CONE"

(2026-07-31, `Threeadic.lean`.) `eq_one_of_smul_eq_mul_localInertia_connected_threeTorsion`
was refuted on 2026-07-29, re-verified independently on 2026-07-30, and the audit — three
screens of it, with the PARI/GP transcript and a measurement of the `39`-declaration upward
cone — ended *"it is not a decision a single prover agent should take by itself, which is why
it is written down here instead of performed."* So it was not performed, and a FALSE `sorry`
with `39` live consumers stayed in the tree while three agents in a row read the audit,
agreed with it, and left.

**Under the loop there is nobody for "not a single agent's decision" to defer to.** An audit
that names its own repair and does not perform it is a task that will never be dispatched,
because every frontier scan sees a leaf with a careful docstring and no defect.

The reason it kept not being done is that the audit priced the repair as *restate the leaf
correctly, then rewire the consumers* — for this cone, four constructor sites and a new
statement nobody had written. **That price is usually wrong.** The cheap realisation:

1. walk UP the call graph from the false leaf to the LOWEST declaration whose own statement
   is TRUE — typically the first one that carries the real object (`hρ : IsHardlyRamified`,
   a pinned `fG`) instead of quantifying over an arbitrary one;
2. replace THAT body with `sorry`, and put the audit, the witness and the true route in its
   docstring;
3. delete everything below it that the usage graph says now has no consumer.

Here that was `exists_connectedEtale_line_of_hopf_package`: `35` declarations and `6373`
lines left the file, two `sorry`s became one, **and nothing above the cut changed at all** —
no consumer was rewired, because every consumer already reached the finite-flat content
through that one theorem. The whole edit is mechanical once the cut point is chosen.

Two details that make step 3 safe, and both are one script:

* compute the dead set by FIXPOINT on the in-file usage graph (strip comments first, attribute
  each token to the enclosing declaration, iterate "no surviving consumer ⇒ dead"), then
  `grep` every dead name across `Fermat/` — cross-file hits are usually prose citations in
  docstrings, which are harmless but must be named in the commit;
* check the range for `instance`/`@[simp]`/`def`/`section` before deleting. Those are the
  elaboration-invisible dependency classes; a range of plain `theorem`s is safe to cut whole.

And name the cut point by asking *is this statement true*, not *is it convenient*. The
boundary in this cone was exactly the boundary between "quantifies over an arbitrary Hopf
order" (false: an arbitrary connected socle can be `3`-dimensional and carry a unipotent) and
"the Hopf order is the flat model of a rank-`2` representation with a residually trivial
quotient" (true: the residual socle is `2`-dimensional for free, which is the sharp bound).

