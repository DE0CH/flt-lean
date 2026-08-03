## A `^variable` GREP TRUNCATES THE INSTANCE LIST — and the scratch then fails as if a hypothesis were missing
(2026-08-02, `flt-lean-206`, mirroring `Deformation.lean`'s section variables into a
scratch.)  The scratch-module rule says to reproduce the target's `namespace`, `open`s
and `variable` block exactly.  The obvious way to harvest the block is
    grep -n '^variable' <the target file>
and it is WRONG, for the reason CLAUDE.md already records about `open` in the hoist
context: **a Lean command continues onto INDENTED following lines.**  Here
    variable {V : Type v} [AddCommGroup V] [Module k V]
      [Module.Finite k V] [Module.Free k V]
is ONE command, and the grep returns only its first line.  The scratch then carries
`V` with two of its four instances, and the failure is
    error: failed to synthesize instance of type class
      Module.Finite k V
repeated at every declaration mentioning `V`, followed by a `(deterministic) timeout at
whnf` once the elaborator starts guessing.  **That reads as "this theorem needs a
finiteness hypothesis the target does not have"** — i.e. as a fact about the
mathematics — and the natural response is to add the instance to your STATEMENT, which
makes the scratch compile and makes the transplanted text WRONG (a stronger hypothesis
the real file's declarations do not carry).
Harvest the block by reading it, or by joining continuation lines first:
    awk '/^variable/{p=1} p&&/^[^ \t]/&&!/^variable/{p=0} p' <file>   # or just sed the range
**The general tell: an instance-synthesis failure on a class the TARGET file's
neighbours plainly use is a mis-copied scope, not missing mathematics.**  Check the
target's `variable` block by eye before touching your own statement — one `sed` of the
line range, and it is the difference between a faithful transplant and a silently
strengthened one.
