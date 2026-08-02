---
name: flt-hoist-inverts-circularity-notes
description: "A \"quoting it would be circular\" / \"X depends on THIS leaf\" note is a claim about POSITION, so a hoist of the cited declaration to an upstream module silently inverts it — and the leaf it protected is then a dead downstream duplicate closable by one `exact`"
metadata: 
  node_type: memory
  type: project
  originSessionId: 2181d7b5-ec88-43f6-88c8-a170e4894ad6
  modified: 2026-08-02T09:05:35.633Z
---

A docstring that blocks a route with a traced circularity — *"`… → exists_x0Model`
→ THIS leaf"*, or *"the same statement without `ab` is `exists_x0Model` (below,
PROVEN — quoting it here would be circular)"* — is asserting where two
declarations SIT. **A hoist moves the cited declaration across a module boundary
and flips the note from true to false, with nothing reporting it**: both files
compile, the leaf still emits `declaration uses 'sorry'`, every ownership check
passes, and the note reads as careful, dated and traced.

Measured 2026-08-02 (`flt-lean-77`) on
`exists_inj_point_x0Model_of_relPointEquiv` in `FreyCurve/MazurTorsion.lean`.
Both notes above were accurate when written, and the tell is the word **`below`**:
`exists_x0Model` had been hoisted into `ModularCurve/X0.lean`, which
`MazurTorsion.lean` `public import`s (line 326). So it is UPSTREAM, Lean forbids
the asserted cycle outright, and its body names only
`exists_x0Compactification_relPoint_inj_x0Model` and
`nonempty_relPointEquiv_of_isX0Compactification_rat`. The leaf closed in three
lines, verified in a 9-second scratch:

    obtain ⟨g, hg⟩ := exists_x0Model N hN h
    exact ⟨g ∘ t.symm, hg.comp t.symm.injective⟩

**Why:** it is the decay in [[flt-cycle-verdict-expires]] one level down — that
entry is about an IMPORT cycle traced through still-open leaves; this is a
DECLARATION-level cycle traced through a declaration that has since moved. Both
are hypotheses about an arrangement, preserved in a form that cannot update
itself, and this one is more persuasive because it names a real chain.

**How to apply.** Two commands, before re-tracing anything:

    grep -rn 'theorem <cited name>' --include=*.lean Fermat/    # which FILE now?
    grep -n 'public import .*<that file>' <your file>           # is it UPSTREAM?

Upstream ⇒ no cycle is possible; read the cited PROOF BODY, not the chain. Treat
"below", "above", "further down" in any docstring as position assertions with an
expiry date.

**And the leaf such a note protects is typically DEAD, which is why it survives.**
Here the sole consumer had one comment-stripped occurrence tree-wide (its own
declaration): a downstream rival cut, per
[[flt-downstream-rival-cut-is-consumerless-by-construction]]. That entry's repair
is "hoist it, do not re-derive it"; **for this leaf no hoist was needed**, because
the upstream theorem had the SAME conclusion under strictly FEWER hypotheses. So
add one step before pricing any such hoist: **diff the downstream statement
against the upstream one and check for subsumption** — identical conclusion plus
a superset of hypotheses means it is a weaker corollary to discharge with one
`exact`, not a rival cut to relocate.

Report the accounting honestly: `−1` direct sorries, `0` mathematics. The
obligation is still owed once, upstream. Closing by delegation was preferred to
deleting the dead pair because deletion strands the PROVEN ~130-line
`exists_weierstrassPointEquiv_of_abelianSchemeStruct`, and disposing of another
agent's proven work is an author's call — see
[[flt-consumerless-leaf-is-dead-or-duplicate]].
