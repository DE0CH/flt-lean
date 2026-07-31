---
name: flt-nonpublic-import-duplicate-cut
description: A non-public import upstream hides a file from every module below it, so two agents cut the same leaf; grep the whole tree for the CONTENT, and a plain import in your own file is the fix
metadata:
  type: project
---

`EllipticScheme.lean` is imported by exactly one module (`X0.lean`) and
**non-publicly on purpose** — a `public import` propagates the reserved token
`over` and truncates any structure with a field of that name. `X1.lean` sits
below `X0.lean` and does not import it at all, so from `X1.lean` every
declaration in `EllipticScheme.lean` is invisible to grep, `#check` and
completion alike.

Result (2026-07-31): `d528fc99` cut the general-field elliptic-scheme leaf in
`EllipticScheme.lean` on 2026-07-30; `f61f3888` cut the SAME content twice more
in `X1.lean` on 2026-07-31, budgeting a "~12 000-line refactor" that was already
done. The three statements share no identifier, so `own.py`, `leafstat.py` and
every frontier scan reported three honest unowned leaves.

**Why:** ownership and duplication checks match on declaration NAMES within a
module's own import cone. A non-public import is a one-way mirror — the
importing module may use the file in proof bodies while everything below it is
blind — so the cone is the wrong search space and the name is the wrong key.

**How to apply:** before cutting a leaf that generalises a base, coefficient
ring or level, grep the WHOLE tree for the concept (`<thing>_field`,
`{k : Type} [Field k]`), not your cone; and check whether the file you are
generalising is imported non-publicly anywhere. If your leaf's STATEMENT does
not mention the hidden module's vocabulary, add a plain (non-`public`) `import`
of it to YOUR file and close the leaf by `exact` — proof bodies reach a private
import ([[lean-private-import-suffices-for-proof-bodies]]). Prefer that to a
re-export in `X0.lean`, which is the hottest file in the tree. Related:
[[flt-inventory-audits-understate-what-exists]],
[[flt-missing-machinery-may-be-downstream]], [[flt-two-leaves-may-be-one]].
