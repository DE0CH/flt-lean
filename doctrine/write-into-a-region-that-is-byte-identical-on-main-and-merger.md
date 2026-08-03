## WRITE INTO A REGION THAT IS BYTE-IDENTICAL ON `main` AND `merger`

(2026-07-31.) The class-7 section above says what an interface split costs. This is the
cheap way to avoid causing one, and it takes two `md5sum`s.

When your target file is one `merger` has heavily rewritten — `HyperellipticJacobian.lean`
was `+1054/-41` against `main` on the day this was written — where you PUT a new declaration
decides whether the merge conflicts, independently of what the declaration says. The check:

    git show merger:<path> > /tmp/m.lean
    sed -n '<merger-lo>,<merger-hi>p' /tmp/m.lean | md5sum
    sed -n '<main-lo>,<main-hi>p'   <path>       | md5sum   # same hash => safe region

Pick a block whose two hashes agree — typically an existing `namespace … end` that neither
side touched — and put the new lemmas and leaves THERE, even if the file's convention would
put them at top level next to the leaf they serve. Then the only edit left in the contested
neighbourhood is the target's own proof body, whose surrounding docstring is usually more
than three lines of unchanged context on both sides, so git never sees a conflict at all.

Concretely, `geomPic_bc_injective` sits ~15 lines below `exists_geomPic`, whose body `merger`
had replaced with a 400-line construction; putting the two new leaves inside `namespace
GeomPic` (identical on both sides) instead of immediately before the theorem turned a certain
conflict into none.

The converse is the warning: **inserting right after a `end <Namespace>` line is the WORST
place**, because that is exactly where another branch's new section will also have been
inserted, and both hunks then anchor on the same context line.

