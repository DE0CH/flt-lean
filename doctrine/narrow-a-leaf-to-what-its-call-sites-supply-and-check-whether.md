## NARROW A LEAF TO WHAT ITS CALL SITES SUPPLY — and check whether the narrowing costs a call site anything
(Same run.  `[CompactSpace T]` → `[IsAffine T]` on
`exists_flatSurj_relPicEquiv_sectionIdealProd`, its consumer, and that consumer's
consumer: three signatures, **zero call-site edits**, one green build.)
The standing rule is that a leaf stated wider than any live call site needs is a
harder theorem than anybody ordered.  Two things make it cheap to act on:
* **Trace the WHOLE chain, not the leaf's own call sites.**  This leaf had one
  consumer, which had two, one of which had one — and all four terminal
  instantiations were `T := J.affineCover.X i`.  Nothing anywhere supplied a merely
  quasi-compact base.  Four `grep`s over comment-stripped source, five minutes.
* **Ask whether the narrowing is INSTANCE-INVISIBLE.**  `IsAffine T → CompactSpace T`
  is an instance and `IsAffine (J.affineCover.X i)` is an instance, so instance search
  finds the affineness exactly where it used to find the compactness: no call site
  changed by a character, and every proof step below that had consumed
  quasi-compactness still had it.  When that holds the narrowing is free; when it does
  not, price the call-site churn before starting, because it is the class-7 interface
  split.
**Say explicitly that the old faithfulness audit is INHERITED and why.**
Strengthening a hypothesis shrinks the class of instances, so a counterexample to the
narrowed form is a counterexample to the old one — the audit transfers in that
direction and only in that direction.  And say what the new hypothesis is load-bearing
FOR: here `[IsAffine T]` is **not** claimed load-bearing for truth (the compact form
is true too), only for the route, where it turns "a gluing over a quasi-compact base"
into "commutative algebra over one ring".
