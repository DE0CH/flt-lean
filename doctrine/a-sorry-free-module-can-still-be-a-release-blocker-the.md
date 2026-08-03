## A `sorry`-FREE MODULE CAN STILL BE A RELEASE BLOCKER: the truncated-header wound

(Release 26, `InvariantCoarseRing.lean`, `HyperellipticJacobian.lean`,
`IsogenyTrace.lean` — three files no branch in the batch had touched, all red on
`merger` before the batch began.)

The shape, and it is what a textual union merge produces when two branches RENAME the
same theorem: the union keeps BOTH headers, the first gets truncated after a binder
line or two, and the second one's orphaned docstring tail lands between them as bare
prose. Lean reports `unexpected token; expected ':'` at the prose line — a *syntax*
error hundreds of lines from anything anyone edited, which reads like corruption rather
than like a merge.

Repairing it is mechanical once seen: delete the truncated header and the orphaned
prose, keep the complete declaration, and **repoint the consumers of the dead name** —
there are usually one or two, and the surviving signature usually accepts them
unchanged (here a `[PerfectField k]` caller supplied `Algebra.IsSeparable` as an
instance). Then look for the *other* half of the same wound: a declaration under the
retired name whose body is byte-identical to the survivor's and which nothing consumes.

**And the same release produced two more instances of the general rule that a signature
can drift out from under a call site with nothing failing until much later:**
`GeomPic.bcDiv_injective` had lost its surjectivity argument and one call site still
passed it; `isDomain_tensorProduct_of_isTranscendenceBasis` had GAINED a separability
argument and one caller did not. In both cases the fix was two characters and the cost
was a build round. **A theorem whose signature you change is not done until
`git grep` over its name is clean** — and if the caller is a branch of a `by_cases`
whose own comment says the other branch covers every case, delete it rather than repair
it. The comment is a licence; use it.

