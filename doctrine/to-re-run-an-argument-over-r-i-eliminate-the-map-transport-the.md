## TO RE-RUN AN ARGUMENT OVER `R ⧸ I`, ELIMINATE THE MAP — transport the ELEMENTS

(2026-07-31, flt-lean-55, on the successor of the leaf in the section below.)

A proof that holds over a domain often extends to a general base by running it over
`R ⧸ I` for every prime `I` and concluding that the obstruction lies in every prime,
i.e. is NILPOTENT. The obvious cost is the induced morphism: if the argument is stated
about an algebra map `Φ : R[W] → R[W']`, you appear to need
`Φ_I : (R⧸I)[W_I] → (R⧸I)[W'_I]`, and the recipe for building one — `AdjoinRoot.lift`
applied to `aeval` at the transported generators, its `eval₂ = 0` side condition
discharged from the transported defining relation, then promoted from a `RingHom` to an
algebra hom — is a real chunk of work with several places to get the universe/instance
plumbing wrong.

**It is usually unnecessary, because the argument does not consume `Φ`.** Read the proof
and list what it actually uses. Here, a 200-line proof used `Φ` in exactly two places: a
defining relation between two ELEMENTS `P = Φ x`, `Q = Φ y`, and one equation saying a
distinguished element is in the image. Restating the theorem with `Φ` deleted and
`P`, `Q`, and the two basis coordinates of the preimage as parameters — same proof,
mechanical substitution — made the base change free, because mathlib already ships
element-level transport (`WeierstrassCurve.Affine.CoordinateRing.map`, with `map_mk` and
`map_smul`) and nothing else was needed. `AdjoinRoot.lift` never appeared.

The general form, and it is worth trying before any transport: **a theorem stated about
a morphism is often a theorem about the images of two or three generators.** Eliminating
the morphism costs one mechanical refactor and buys base change, specialisation, and
reuse at other maps that were never constructed.

Two corollaries from the same run:

- **`IsDomain` was never the real hypothesis; `IsReduced` was.** Once the argument is
  element-level, the prime-quotient sweep upgrades the domain theorem to reduced rings
  outright — nilpotent means zero there — for about 20 lines. So before pricing the
  general case, check whether the *reduced* case is already free; it splits the leaf
  into a part you can close today and a residue that is purely infinitesimal.
- **State the residue as a HYPOTHESIS on the remaining leaf, not as prose in its
  docstring.** `IsNilLinearShape P Q` (the four coefficient families, each nilpotent) is
  now an argument of the leaf and is discharged at the call site. A prose paragraph
  saying "the coefficients are known to be nilpotent" is unenforced and rots; a
  hypothesis is checked by the compiler and makes the leaf strictly weaker, so the next
  owner cannot accidentally re-prove the part that is done.

