## A RED UPSTREAM MODULE DOES NOT BLOCK A CUT THROUGH IT — SHIM THE RELEASE OLEAN, AFTER DIFFING THE ONE NAME YOU USE
(2026-07-31, `flt-lean-389`, on `exists_cubeModel_pic_of_infinite`.) The cheapest correct
cut of a leaf routinely runs through a theorem in another module — here, closing
`HyperellipticJacobian.lean`'s geometric Mordell–Weil half by importing `X0.lean`'s PROVEN
`exists_cubeModel_of_abelianScheme` instead of re-cutting the same sheaf-level obligation.
**That module can be RED at your base**, and it was: `X0.lean` at `merger` `9e7f6e4b` fails
with **103 errors** (release 27 did not publish; `merger` has since gained
`1ead8a94 … why it did not publish, and the X0 repair method`). The obvious readings —
"take the other cut", "wait for the repair", "commit unverified" — are all wrong.
**Verify against the RELEASE SNAPSHOT's olean.** `~/.flt-release-lake/build` holds the
last green build and `~/.flt-release-lake/sha` names its commit. Your edit is checkable
against it **exactly when every name your new text takes from the red module has a
byte-identical STATEMENT at that sha and at your HEAD** — one `git show` per name:
    for R in $(cat ~/.flt-release-lake/sha) HEAD; do
      git show $R:<the red module> | grep -A6 "^theorem <the one name you use>"; done
Here that was a single name and the two outputs matched character for character, so the
shim proves what a real build would. Then (per the existing shim recipe) farm YOUR
worktree's current, mutually consistent oleans and override only the red module:
    cp -rs /scratch/chend-flt/flt-lean-N/.lake/build/lib/lean /tmp/relean-N/
    rm -f /tmp/relean-N/lean/<path>/X0.olean*
    cp -f ~/.flt-release-lake/build/lib/lean/<path>/X0.olean* /tmp/relean-N/lean/<path>/
    LP=$(lake env printenv LEAN_PATH); LSP=$(lake env printenv LEAN_SRC_PATH)
    LEAN_PATH="/tmp/relean-N/lean:$LP" LEAN_SRC_PATH="$LSP" lean <your file>
**Two conditions make this sound rather than wishful, and both must be checked:**
* *the farm must be internally consistent* — take the CURRENT build as the base and
  override ONE module, not the other way round. A wholesale release-era farm would compile
  your file against release-era versions of its other dependencies; here three of the
  target's dependencies had changed since the snapshot, so that would have proved nothing;
* *the overridden olean's own dependencies must not have moved under it*. `git diff` the
  STRUCTURES your borrowed theorem's statement mentions — not the whole files. Here
  `ProjectiveHeight.lean` and `AbelianScheme.lean` had both changed, but `CubeModel`,
  `AbelianSchemeStruct` and `RelPoint` were untouched (the diffs were an added theorem and
  an unrelated pairing repair), which is what makes loading the old `X0.olean` beside the
  new ones safe.
**And weigh the marginal damage before adding the edge at all.** A green module gaining an
import of a red one sounds reckless; compute who is downstream. `HyperellipticJacobian`'s
only consumer is `MazurTorsion.lean`, which already `public import`s `X0.lean`, so while
`X0` is red that consumer is red anyway and the marginal cost of the new edge is exactly
one module's warning set. If instead the red module sits under something that still builds,
do not add the edge.
Two riders from the same run:
* **Put a one-consumer helper DOWNSTREAM, not beside the structure it is about.**
  `CubeModel.congr` (transport of a `CubeModel` along an `AddEquiv`) belongs in
  `ProjectiveHeight.lean` next to `CubeModel`. It is in `HyperellipticJacobian.lean`
  instead, because `ProjectiveHeight.lean` is `public import`ed by `X0.lean`, so touching
  it rebuilds the largest module in the tree — **and the rebuild had already been started
  and would have had to be thrown away.** Dot notation is the price (`cubeModelCongr cm e`
  rather than `cm.congr e`, since a declaration made inside `Fermat.Hyperelliptic` cannot
  extend the `Fermat.CubeModel` namespace); say in the docstring where it belongs and what
  would justify the hoist.
* **A non-public `import` is the right edge for a proof-only dependency, and it is worth
  spelling out why in the import block.** `X0.lean`'s 107 000 lines of names are used here
  only inside one theorem BODY, which a private import reaches; making it `public` would
  re-export all of them through a module whose consumer already has them. What the edge
  still costs is BUILD ORDER, and that is the thing to justify.
