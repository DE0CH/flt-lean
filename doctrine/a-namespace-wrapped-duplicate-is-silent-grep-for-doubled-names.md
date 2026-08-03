# A namespace-wrapped duplicate is SILENT — grep for doubled declaration names after every big merge

(Release 35, 2026-08-03.) The 387-branch batch left the ENTIRE zeta chain — 91
declarations, ~1750 lines, from `galoisFieldSpecHom` to
`exists_frobEigenvalues_pointCount_of_isProperSmoothCurve` — in `X0.lean`
TWICE, byte-identical including docstrings: once inside `namespace Fermat`,
once inside `namespace GaloisRepresentation.Modularity` (the wrapper it had
carried in `Interface.lean` before flt-lean-358's prescribed relocation was
performed twice by different routes). Lean raised NO error: the full names
differ, so this is legal code. Nothing in the build output distinguishes it
from intent.

Costs while it lived: ~1750 lines of double elaboration in the tree's biggest
file, and — the actual tell — TWO frontier leaves counted twice
(`eulerCount_eq_effectiveDivisorCount`,
`exists_riemannRochGrowth_of_effectiveDivisorCount`), which would have
dispatched two provers each onto phantom twins whose closure the other copy
never sees.

Lessons that generalize:

- **`flt-frontier.py --names | sort | uniq -d` is a one-line damage detector.**
  A duplicated name on the DIRECT frontier means either a namespace-wrapped
  copy (this class) or deliberate twins (level-specific `torsion_pic` at two
  `PlaceData` coefficient sets — legitimate). Check which BEFORE dispatching a
  prover at either.
- **Deletion needs a tree-wide consumer scan per copy, qualified AND
  unqualified.** Here the `Fermat.*` copy had zero consumers and the
  `GaloisRepresentation.Modularity.*` copy had exactly two, both qualified,
  both in the Eichler–Shimura cluster — so the FIRST copy (in the file's own
  ambient namespace, the one that looks canonical) was the dead one. Do not
  assume the wrapper copy is the stray.
- **A relocation "performed" on a branch can be half-performed on the merged
  tree.** The same release found `exists_x0Compactification_finiteField` moved
  but the rest of its 2124-line block stranded 24k lines down, with the
  in-file docstring still announcing the completed hoist. When a docstring
  says "hoisted VERBATIM" and the compiler says unknown identifier, the merge
  kept the pre-hoist order for part of the block: REPLICATE the branch's
  documented hoist (its dependency measurement usually still holds — re-probe
  with a comment-stripped token scan), don't invent a new arrangement.
