## A DOCSTRING THAT ARGUES TWO LEAVES ARE EQUIVALENT IS A LEAF-MERGE WAITING TO BE PERFORMED

(2026-07-31, `flt-lean-217`, and it closed two leaves for 30 lines of Lean.)

`X1.lean` carried two open citation leaves, `exists_gamma1RigidifiedModuliScheme`
(`∃ R`) and `isAffine_of_gamma1RigidifiedModuliScheme` (`∀ R, IsAffine R.M`), split
out of one node the day before. The second one's docstring contained this, under the
heading "Why the `∀` is legitimate":

> `universal` is a **fine** moduli property, so any two inhabitants are related by a
> unique isomorphism … `IsAffine` is invariant under isomorphism of schemes. So
> "the Katz–Mazur `𝔐(𝒫, 𝒮)` is affine" and "every inhabitant … has affine `M`" are
> the same statement.

That paragraph was written to *justify the quantifier* — and it is simultaneously a
complete proof that the two leaves are ONE leaf. Nobody read it as one, because it
sits under a heading about faithfulness. Writing it in Lean
(`nonempty_iso_gamma1RigidifiedModuliScheme`: feed each scheme's universal family to
the other's `universal`, then kill both round trips with `universal`'s uniqueness
clause applied to the scheme's OWN universal family) is 30 lines over
`IsBaseChangeOfGamma1.refl`/`.comp`, and it collapses `∃ R` + `∀ R, IsAffine R.M`
into the single `∃ R, IsAffine R.M`. Both names and signatures survive as theorems,
so no consumer changed.

**So: prose of the form "these are the same statement", "this follows from that by
rigidity/uniqueness/invariance", "legitimate as a `∀` because …" is a proof sketch,
not a caveat.** If it is right, one of the two leaves is free. Grep the file's
faithfulness sections for it before dispatching anyone at either leaf.

The structural version, worth checking whenever a structure has a fine-moduli or
universal-property field: **a `∃!`-valued field makes the structure a contractible
groupoid, so `∀ R, P R.M` and `∃ R, P R.M` coincide for every isomorphism-invariant
`P`.** The same merge is available verbatim on the `Γ₀` side of this development
(`X0.lean`'s `exists_rigidifiedModuliScheme` / `isAffine_of_rigidifiedModuliScheme`
over `RigidifiedModuliScheme`, whose `universal` is the same shape and carries no
`m ≫ strM = g` conjunct, so the transcription should be shorter). It was not done
from `flt-lean-217` because that file is owned separately.

Related, and the reason the 2026-07-30 split happened at all: the split's own
docstring recorded the trade honestly as "`1 -> 2` open leaves, not `1 -> 1`". A
split that ADMITS it raises the count is exactly the place to ask whether the second
residue is real, because a leaf that a sibling's docstring can already derive is not
a citation — it is unwritten Lean.

