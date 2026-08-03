## A REPOSITORY NAMED AFTER A THEORY IS A STATEMENT OF INTENT — CHECK FILE SIZES, NOT THE NAME
(2026-08-02, `flt-lean-260`, auditing the vendoring route for `isLocalTateDual`.)
`Mathlib/RingTheory/Valuation/Discrete/Basic.lean:57` carries a docstring pointer to
`github.com/mariainesdff/LocalClassFieldTheory`, and five separate audits of this leaf
(2026-07-27 through -31) had recorded "local class field theory is absent from the pin"
without ever opening it. The obvious inference — *a repo called LocalClassFieldTheory
contains local class field theory, so vendoring it is the cheap route* — is wrong, and
the decisive fact takes one API call:
    curl -sL "https://api.github.com/repos/OWNER/REPO/git/trees/master?recursive=1" \
      | python3 -c "import json,sys; [print(t.get('size'), t['path']) for t in json.load(sys.stdin)['tree'] if t['path'].endswith('.lean')]"
`ClassFormation/ClassFormation.lean` — the ONE file whose name promises the invariant
map — is **2 bytes**. An empty placeholder. Everything real in the repo (~275 kB) is
DVR / local-field / spectral-norm foundations, i.e. strictly BELOW the theory the name
advertises, and its own README says "local fields, and **eventually** LCFT".
**The generalisable checks, cheapest first, before costing any vendoring route:**
* **`ls` the tree WITH SIZES.** A directory listing alone would have shown a
  `ClassFormation/` and read as a hit; the size is what refutes it. Aspirational
  scaffolding is normal in a research formalization and is invisible to a name search.
* **Read the BLUEPRINT, not the README.** `blueprint/src/content.tex` states what is
  actually claimed, chapter by chapter. This one's scope list excludes the invariant
  map, the Brauer group, Galois cohomology, `H²`, reciprocity and Tate duality — i.e.
  it says in the project's own words that the name is a goal.
* **Check the pin before anything else if you are still tempted.** `lean-toolchain` and
  `lake-manifest.json` are two `curl`s: `v4.22.0-rc2` / mathlib `81a4b04c` against our
  `v4.32.0-rc1` / `a3364fae` is ten toolchain releases, which sinks a vendoring route on
  its own however good the content is.
This is [[flt-inventory-audits-understate-what-exists]] running in REVERSE — there an
absence claim is too pessimistic, here a POINTER is too optimistic — and the reverse
direction is worse, because a pointer in mathlib reads as an endorsement. **Record the
verdict on the leaf**, with the file size, so the sixth audit does not re-run it.
