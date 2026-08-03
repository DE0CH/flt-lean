## A BUNDLED STRUCTURE'S OBJECT FIELDS MAY CARRY NO CONTENT — TEST WITH AN `iff` FIRST

(2026-07-31, `flt-lean-15`, on `exists_eisensteinFormalImmersionAt` in
`ModularCurve/X0.lean` — the section above is the same failure in a different suit,
and the two together are worth reading as one rule.)

This development cuts leaves by BUNDLING: a leaf produces a `structure` whose fields
name the inputs of the textbook argument, so that "a partial advance on any one of them
is visible". `IsEisensteinFormalImmersionAt` is the archetype — five object fields
(`Eis`, `EisRed`, `ajE`, `ajE'`, `redE`) spelling out Mazur's Eisenstein quotient
`J_e(p)(ℚ)`, its reduction, and the two Abel–Jacobi maps — and **four separate audits
recorded IRREDUCIBLE on the strength of them**: "`J_0(p)`, the Hecke algebra, the
Eisenstein ideal and reduction of an abelian variety are all missing."

All four were auditing a *docstring*. `Eis` and `EisRed` are bare `Type`s under an
existential, so they can be taken to BE the special fibre, with `ajE = redX` and
`ajE' = redE = id`; `red_ajE` is then `rfl` and `redE_inj` is `Function.injective_id`.
The whole structure is inhabited **iff** two conditions on `redX` alone hold —
injectivity on the cuspidal locus, and `cusp_lift`. No abelian variety is asked for
anywhere in the statement. The `iff` is nine lines and now sits in the file.

**The check, and it costs one theorem.** Before believing that a bundled leaf needs a
missing THEORY, ask which of its fields are pinned by the others and which are free:

- a field of type `Type` (or any `Sort`) inside an existential is FREE — nothing
  outside the structure can observe it, so it can be instantiated at anything already
  in scope, usually the object the leaf is quantified over;
- a field whose value is forced by a stated equation (`red_ajE` here) is free once
  its neighbours are chosen to make that equation `rfl`;
- an injectivity/faithfulness field is free at the identity;
- what is NOT free is any field constraining data the leaf receives as a HYPOTHESIS —
  here `redX`, which arrives inside `IsX0JReductionAt` and is what the leaf really
  demands a theorem about.

Then state the reduced form and PROVE the `iff`. If it goes through, the reduced form
is the honest target and the anatomy was decoration; if it does not, you have learned
exactly which field is load-bearing. Either outcome is worth the theorem.

**This is NOT a way to make a leaf cheap, and expecting that is the trap on the other
side.** The reduced form here is still Mazur — the two junk reductions that `red_jm`
permits each die against the condition the other satisfies, and (A) ∧ (B) at `q`
already imply that no rational point of `Y_0(p)` has a `j`-pole at `q`. What the
reduction buys is that the next prover is not sent to build `J_0(p)`, the Hecke
algebra and the Eisenstein ideal in order to discharge fields that `id` discharges.
Vacuous OBJECTS, undiminished CONTENT: keep the two apart when reporting.

Corollary for writing new bundled leaves: the argument that bundling "leaves the least
for a prover to invent" is right about the fields that are pinned and wrong about the
free ones, and the free ones are pure noise in the statement. Carry the anatomy in the
DOCSTRING, where it costs nothing and misleads nobody, and keep it in the type only
where something outside the structure observes it.

