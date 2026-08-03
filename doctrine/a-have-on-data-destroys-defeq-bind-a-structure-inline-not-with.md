## A `have` ON DATA DESTROYS DEFEQ — bind a structure INLINE, not with `have`
(Same task, one iteration.) `have h : T := v` **forgets `v`** when `T` is data, so a
composite of two `def`s bound that way stops being definitionally what it was. Concretely:
    have jacP : IsJacobianOf strC ab' o := (P.isAlbaneseOf hf).isJacobianOf
    have hP' : jacP.aj g x = jacP.aj g y := hP     -- FAILS
    -- Type mismatch: hP has type P.aj x = P.aj y but is expected to have type
    --   jacP.aj g x = jacP.aj g y
`IsRelPicZeroOf.isAlbaneseOf` and `IsAlbaneseOf.isJacobianOf` are plain `def`s, so
`(P.isAlbaneseOf hf).isJacobianOf.aj g x` really is defeq to `P.aj x` — and `have` is
exactly what breaks it. Keep the composite inline (`obtain … := (P.isAlbaneseOf hf).…
.universal …`) and close the last goal with `congrArg` rather than `rw`, which needs a
syntactic match the projections will never give you. Use `let` only if you must name it.
This development binds structures with `have` all over the place and usually gets away
with it, because most such structures are only ever *projected*. It bites precisely when
you need the projection to be DEFEQ to something else — i.e. whenever you have built the
same object by two routes, which is the commonest shape of an autoduality or
universal-property transfer.
