---
name: flt-print-axioms-works-from-importer
description: "#print axioms DOES work from a scratch module importing the target in this project (13 s vs re-elaborating the declaring file) — always run a known-sorried control"
metadata: 
  node_type: memory
  type: project
  originSessionId: c721205d-ec56-41c7-9bdc-015e4570494b
  modified: 2026-08-01T07:01:52.097Z
---

(2026-07-31, `flt-lean-135`.) CLAUDE.md's standing rule says `#print axioms`
must be appended to the file that DECLARES the name, because the module system
elides imported proof bodies. That holds for a `module` file WITHOUT
`@[expose] public section`; **every project file here has one**, so a scratch
that `public import`s the target answers correctly:

    module
    public import Fermat.FLT.FreyCurve.MazurTorsion
    #print axioms <your target>
    #print axioms <a KNOWN sorried declaration in the same file>   -- the CONTROL

**13 seconds** against a 15-to-40-minute re-elaboration of an 80k-line module.

**Always include the control.** An importer whose traversal found nothing would
report everything clean, which is exactly the failure the original rule was
written about; one known-sorried name from the same file separates the two in
the same run (it must come back with `sorryAx`).

Caveat: the scratch reads the OLEAN, so it answers about the last BUILD, not
about unsaved edits. `lake build` the module first.

Related: [[flt-route-residue-is-the-cheap-route]].
