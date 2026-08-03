## port leaves check for proven twins

(Cut verbatim out of CLAUDE.md's `THE GOAL: fully formalize Fermat's Last Theorem, no sorry, n` section at the 2026-08-03 doctrine split; nothing reworded.)

**The MIRROR IMAGE of the fourth class, and it wastes agents rather than hiding
sorries: a module GREEN AND COUNTED, but unreachable from the file that needs it**
(2026-07-31, `flt-lean-387`). `exists_ellipticScheme_weierstrassChart_addEquiv_field`
was priced — by its own docstring, by its task prompt, and by the assigned agent's
own first inventory — as a ~6500-line `ℚ → arbitrary field` port of 106 declarations.
Two of its four inputs were **already proven over an arbitrary field, sorry-free**, in
`Fermat/FLT/Mathlib/AlgebraicGeometry/EllipticCurve/ProjectiveModelOverField.lean`
(103 declarations, namespace `WeierstrassCurve.Projective.OverField`), along with most
of a third. One `public import` closed them.

That module is *reachable from `Fermat.lean`* — via `MoretBailly.lean`, its only
consumer — so it compiles, is green, and is counted by every instrument. It was
invisible **only from `EllipticScheme.lean`**, which did not import it. So the fourth
class's diagnostic does not fire here, and neither does anything else: **`lake build
<YourModule>` is evidence of absence for your import cone and for nothing else.**

This bites hardest on PORT leaves ("generalise this proven `ℚ` theorem to a field"),
because a port's twin is named from the generality (`…OverField`, `…_field`,
`…OverRing`) rather than from the consumer's vocabulary, so a name grep misses it
while a conclusion grep finds it instantly:

    grep -rn "SmoothOfRelativeDimension 1 (projToSpec" Fermat/ --include=*.lean

**So before cutting or accepting any port/generalisation leaf: grep the whole tree for
the CONCLUSION's shape, then check whether your file imports the hit.** A
`Fermat/FLT/Mathlib/...` module usually imports only mathlib plus one sibling, so
importing it rarely cycles. Two traps when delegating: the ported twin may take the
base field EXPLICITLY where the `ℚ` version leaves it implicit; and opening its
namespace unrestricted can drag in scoped notation that collides — here `open
_root_.WeierstrassCurve.Projective` made `(E⁄F).Point` an `Ambiguous term` against
`WeierstrassCurve.Affine`'s `⁄`, fixed by opening a name list instead.

Second trap, same day: a naive `grep sorry` over sources counts the word
inside DOCSTRINGS, and this development's docstrings discuss sorried leaves
constantly. That inflated a scan to 144 "sorried declarations" against a
true 85. Any frontier scan must strip block comments (nested `/- -/`) and
line comments first, then attribute each surviving token to its enclosing
declaration by walking BACKWARDS to the nearest declaration header —
walking forwards mis-attributes a later declaration's sorry to an earlier
proven one, which is exactly how `exists_hardlyRamifiedLift` was twice
mislabelled open when it is proven.

Related: stale `(sorry leaf)` / `(sorry node)` docstring LABELS on
now-proven declarations are a third source of phantom work, since leaf
lists get harvested from them. Correct them when found rather than leaving
them to mislead the next dispatch.

