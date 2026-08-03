## A `variable` USED ONLY IN A PROOF BODY IS NOT INCLUDED — one root cause, thirty-four errors

(2026-07-31, `flt-lean-105`, on inherited work that had never been compiled.)
Lean 4 includes a section `variable` in a declaration only when the variable occurs
in that declaration's **statement** (or is an instance-implicit). A hypothesis used
solely inside the proof is simply not there:

    variable (hv : v ≫ d.f = d.f) (hadd : IsAdditiveOn d.ab d.ab v hv)

    theorem add_fixed {x y : RelPoint d.f g}
        (hx : x.1 ≫ v = x.1) (hy : y.1 ≫ v = y.1) : (d.ab.add x y).1 ≫ v = … := by
      rw [hadd x y, …]        -- error: Unknown identifier `hadd`

**The reason this is worth a section is the BLAST RADIUS.** Six declarations in one
block were affected, and because each then had the wrong arity, every later
reference to them failed too: **34 errors from one cause**, almost all of them
`Application type mismatch` or `Function expected at` pointing at call sites that
are individually correct. Chasing them one at a time is hours; the fix is six
`include` lines. So when a block reports a cloud of arity errors, look for
`Unknown identifier` on a *section variable* in the FIRST error, not the loudest.

Three mechanics, each of which cost a round here:

* **Scope the `include` per declaration, not per section.** `include hv hadd` as a
  bare command after the `variable` line over-includes: a sibling whose statement
  already mentions `hv` (so `hv` was auto-included) now silently gains `hadd` too,
  and its call sites fail with `Invalid projection … has function type` — a message
  that says nothing about arity. Use `include hv hadd in` on exactly the
  declarations whose *bodies* need them.
* **`include … in` goes ABOVE the docstring.** Between the docstring and the
  declaration it is `unexpected token 'include'; expected 'lemma'`.
* A `def` whose result is a class (`Group …`, `AddCommGroup …`) wants
  `@[reducible]`, or Lean warns.

And the standing rule this violates: **work you inherit has not been compiled until
you compile it.** The block carried a careful docstring, a correct design and a
plausible proof, and it had never elaborated once.

### Verifying against the RELEASE olean when the target's own cone is red

The same run could not build `MazurTorsion` at all, because `X0.lean` was red from
merge damage. The block was still verified, in ~90 s per iteration, by the shim the
scratch-module section above describes — with the release snapshot as the source of
the one olean that mattered:

    cp -rs ~/.flt-release-lake/build/lib /tmp/relean-N/          # symlink farm, instant
    LP=$(lake env printenv LEAN_PATH); LSP=$(lake env printenv LEAN_SRC_PATH)
    LEAN_PATH="/tmp/relean-N/lib/lean:$LP" LEAN_SRC_PATH="$LSP" lean Scratch.lean

**This is sound only under a check you must actually run**: every name the block
uses has to be present and unchanged at the snapshot's sha (`~/.flt-release-lake/sha`).
Here that was seven names, all of them older than the release, so the shim proved
exactly what a real build would have. It is NOT a substitute when your block
consumes something added since — then the shim's `X0` is a *different theory* and a
green scratch means nothing. Check the names first; it takes one `git show`.

