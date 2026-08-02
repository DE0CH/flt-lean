---
name: flt-downstream-rival-cut-is-consumerless-by-construction
description: "A leaf's whole machinery can be built DOWNSTREAM of the file that owns the leaf — where it is consumerless by construction and invisible to every scan; hoist it, do not re-derive it"
metadata: 
  node_type: memory
  type: project
  originSessionId: b822d9f6-76c8-4b7b-be13-c67665b5e9c0
  modified: 2026-08-01T17:36:04.524Z
---

`X0.lean`'s `exists_x0Compactification_relPoint_inj_x0Model` (the `X_0(N)(ℚ) ↪ N a 1(ℚ)`
moduli dictionary) carried a "WHAT A SUCCESSOR MUST BUILD" list of three items, each
correctly described as absent from mathlib, from `~/cs/FLT` and from this project. **Two of
the three had been PROVEN the day before** — as
`exists_weierstrassPointEquiv_of_abelianSchemeStruct` and
`exists_point_map_eq_of_galoisFixed` in `FreyCurve/MazurTorsion.lean`, which is DOWNSTREAM
of `X0.lean`. Beside them sat a strictly finer open leaf and an assembly, i.e. a complete
RIVAL CUT of the upstream leaf, built where it could never serve it.

**Why the downstream copy is guaranteed to be dead.** The parent lives upstream, so no
proof term reaches the cluster: a comment-stripped grep found
`exists_relPoint_inj_x0Model_of_abelianSchemeStruct` at its own declaration and in
docstrings only. Every instrument reports it as ordinary open work — it compiles, emits
`declaration uses 'sorry'`, is counted by the frontier scan, and passes the three-part
ownership test — while the LIVE leaf upstream still carries the whole geometry.

**Why:** an absence claim in a docstring is scoped to the import cone it was written in,
and a downstream module is precisely where a general-purpose bridge gets built, because
that is where its first consumer appears. The upstream author cannot see it and the
downstream author has no reason to look up.

**How to apply.** When dispatched at a leaf whose docstring prices a "none of this exists"
list, grep the WHOLE tree for the CONCLUSION's shape before believing it —
`grep -rn 'RelPoint' --include=*.lean Fermat/ | grep 'toAffine.Point'` found all of this in
one command, where no name-based search could. Then, if the machinery is downstream:

1. check every dependency of the block resolves from the target's cone — a scratch module
   importing ONLY the upstream file, with the block pasted verbatim under primed names,
   settles it in seconds;
2. check declaration ORDER — every in-file dependency's line must be above the insertion
   point (here the deepest was 47250 against an insertion at 113311);
3. move the block VERBATIM by line range and DELETE it from the source in the same commit,
   or the identical namespace makes it a `has already been declared` error;
4. receipt: the combined sorted line multiset of the two files must be unchanged.

The trade is worth stating plainly: the frontier count does not move in the upstream file
(one leaf closes, the finer one opens) and drops by one downstream, and what changes is that
the LIVE obligation became the small one. See [[flt-hoist-above-the-consumer-not-a-new-theorem]]
for the module-split variant and [[flt-consumerless-leaf-is-dead-or-duplicate]] for the
detection habit.
