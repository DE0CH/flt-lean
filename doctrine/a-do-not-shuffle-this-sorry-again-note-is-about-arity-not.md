## A "DO NOT SHUFFLE THIS SORRY AGAIN" note is about ARITY, not vocabulary

(2026-07-31, `IsogenyTrace.lean`.) Seven passes moved that file's single `sorry` around a
circle of mutually equivalent statements about the degree of an isogeny — `deg = det` on the
`ℓ`-torsion, the characteristic polynomial, the shift expansion, the parallelogram law, Weil-pairing
adjointness. The file then wrote, correctly, "the two statements are **equivalent**, so nothing is
gained or lost by moving between them, and a future pass should not shuffle them again." Every one of
those restatements really was a lap of the same circle.

The eighth pass found a genuine move anyway, and the discriminator generalises: **every member of the
circle quantified over a PAIR** — two endomorphisms `(φ, ψ)`, or an endomorphism and a prime `(ψ, ℓ)` —
**and the new target quantifies over ONE.** The whole parallelogram law
`deg(φ+ψ) + deg(φ−ψ) = 2 deg φ + 2 deg ψ` follows, unconditionally, from its single instance `φ = 1`,

    deg(χ + 1) + deg(χ − 1) = 2 deg χ + 2,

by a second-order recurrence in `m` for `deg(χ + [m])` and then multiplication by `φ̂`, which converts
the pair `(φ, ψ)` into the pair `(φ̂ψ, [deg φ])`. That is not a lap: the hypothesis mentions no second
endomorphism, no prime, no module, no determinant and no pairing, and it is the shape the classical
`x`-coordinate degree count actually produces, since that count runs one endomorphism at a time.

**So before accepting an "equivalent, do not shuffle" verdict, count the binders on each form.** A
restatement that keeps the arity is the lap the note is warning about; one that drops it is a
reduction, and the note does not cover it. Record the arity when writing such a note, so the next pass
can tell which it is holding.

**Corollary, from the same pass: an "irreducibility" audit is only as wide as the axis its author
searched — and the axis is usually the one the counterexample lives on.** That file's `ℤ[√2]`,
`q := |N|` model shows the five available facts about `deg` cannot give the parallelogram law, and it
is correct. It was checked here against two further facts it does not cover, and it survives both:
`End W` is in fact COMMUTATIVE in characteristic zero — the differential character
`λ : End W → F` of `DifferentialCharacter.lean` is an injective ring homomorphism, so the comment on
`IsogenyTrace.lean`'s `Mathlib.Tactic.NoncommRing` import ("`End W` is a NONcommutative ring") is
mathematically false — though the import must STAY, since no `CommRing (End W)` instance is registered
and `ring` cannot know — and the dual is an involution with `deg ψ̂ = deg ψ`. `ℤ[√2]` has both. What it does
*not* have is a finite unit group, and `{ψ : deg ψ = 1} = Aut W` is finite; so **finiteness of `Aut W`
is a candidate substitute for the missing geometric input**, and it is the only one that pass found.

