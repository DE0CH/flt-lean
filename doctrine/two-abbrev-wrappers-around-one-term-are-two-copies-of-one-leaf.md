## TWO `abbrev` WRAPPERS AROUND ONE TERM ARE TWO COPIES OF ONE LEAF — and no scan can see it

(2026-07-31, `RelativePicard.lean`.) `presheafModPullback h` and `presheafPullback h`,
defined ninety lines apart in the same file, are both
`PresheafOfModules.pullback (Scheme.Hom.toRingCatSheafHom h).hom` — the same term written
once with dot notation and once without. Each carried its own sorried theorem
(`nonempty_presheafModPullback_tensor`, `nonempty_presheafPullback_tensor`) whose
statements differ only in the names of their bound variables. Two agents cut the same leaf
out of the same parent on the same day and neither could see the other's copy.

**Every frontier instrument counts DECLARATIONS**, so this reads as two leaves for as long
as the wrappers stand: `flt-frontier.py`, the `declaration uses 'sorry'` warning set, and
the census all agree, and they are all wrong. `own.py`/`leafstat.py` cannot help either —
the names are genuinely different. Only unfolding the wrappers shows it.

So when a file defines a thin `abbrev` "for readability", check whether an earlier one
already denotes the same term. The cheap mechanical check is to elaborate both and ask for
`rfl`:

    example : presheafModPullback h = presheafPullback h := rfl   -- it was

Related and more general: a wrapper hides identity exactly as well as it hides complexity.
`[[flt-two-leaves-may-be-one]]` is the sibling case where two leaves are logically, not
definitionally, the same; this one is worse because no mathematics is involved at all.

