---
name: flt-verify-a-relocation-in-a-destination-scratch
description: Verify a relocated block in a scratch that imports ONLY the destination module — 10 seconds against 5 minutes, and it answers the import-surface question exactly
metadata:
  type: project
---

To move 1749 lines from `Interface.lean` into `X0.lean`, the whole verification is
a scratch whose imports are exactly the destination module's own — `public import
Fermat.FLT.ModularCurve.X0` plus X0's single non-public import — followed by the
destination's `open`/`namespace` preamble and the block. It elaborated in **10
seconds**; a real `lake build` of X0 is 310 s and of `Interface.lean` far more.

**Why:** the doctrine's warning that "a clean scratch is no evidence about the
target file's import surface" is about a scratch that declares its OWN convenient
imports. A scratch that declares *the destination's* imports is the opposite: it
is exactly as strict as the destination, so a green run really does mean the block
compiles there. It answered the live question — whether X0 needed any of the 84
Mathlib modules `Interface.lean` has and it does not — with a flat no, without a
single X0 rebuild.

**How to apply:** copy the destination's `module` / `public import` / `@[expose]
public section` / `universe` / `open` / `namespace` preamble verbatim, paste the
block, run `lake env lean Scratch.lean`. Add the destination's *non-public* imports
too — those are visible inside the file's body and not to an importer, so omitting
them makes the scratch stricter than reality and manufactures errors. Then add any
third module you suspect of a name collision (see
[[flt-relocation-collides-with-a-third-file]]) — importing it into the scratch is
how a duplicate declaration surfaces in seconds rather than at the far end of a
downstream build. Delete the scratch before committing.
