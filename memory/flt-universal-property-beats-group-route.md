---
name: flt-universal-property-beats-group-route
description: A leaf quantified over "all abelian schemes A" usually reduces to a statement about the SOURCE alone — IsJacobianOf.universal is the Albanese property and is already in X0.lean
metadata:
  type: project
---

When a leaf reads *"every morphism from `C` into an arbitrary abelian scheme `A`
is constant"*, do not build the route its docstring recommends before checking
whether the file already has a UNIVERSAL PROPERTY that eliminates `A`.

`exists_section_of_rationalProperCurve_toAbelianScheme`
(`Fermat/FLT/ModularCurve/X0.lean`) was proven on 2026-07-31 this way. Its own
audit priced the group-theoretic route — *"a pointed morphism from a connected
group variety to an abelian variety is a homomorphism, with `Hom(𝔾_a, A) = 0`"* —
which would have needed a group-scheme structure on `𝔸¹` that does not exist
here. None of that was necessary: `IsJacobianOf.universal` **is** the Albanese
universal property, so a POINTED natural transformation on relative points
factors through `aj` for free, and all that is left is that `aj` itself is
constant — a statement about the curve alone, with no `A` in it.

**The reusable shape**, and every step of it is PROVEN material in that file:

1. get a base point (here: the origin of `𝔸¹` pushed along `j`);
2. `exists_relPicZero` (`ModularCurve/RelativePicard.lean`, upstream) →
   `IsRelPicZeroOf.isAlbaneseOf` → `IsAlbaneseOf.isJacobianOf`;
3. translate the given morphism on the FUNCTOR OF POINTS —
   `c g x := Ψ(x) − Ψ(o)` using `ab.add`/`ab.neg` — rather than translating the
   scheme (`AbelianSchemeStruct.translate` is declared ~30 000 lines lower and
   is not needed). Naturality is `pre_add` + `pre_neg`; pointedness is
   `neg_add`;
4. `jac.universal` → `(c g x).1 = (aj g x).1 ≫ u`;
5. constancy of `aj` makes the right side independent of `x`; cancel the
   translation with `add_right_cancel` in `AbelianSchemeStruct.addCommGroup`.

**The price, and it is worth naming**: the declaration now depends on the
relative-Picard cone where before it depended on nothing. That is the right
trade in this project — the same cone is consumed by every other Jacobian
statement — but it is a real coupling and belongs in the commit message.

Two smaller facts found along the way: `AbelianSchemeStruct.pre_neg` already
exists (X0.lean ~8494) so do not re-derive it, and `RelPoint.post_pre` is
declared far BELOW the rigidity leaves, so inline it as
`Subtype.ext (by simp [RelPoint.post, RelPoint.pre])` instead.

See also [[flt-two-leaves-may-be-one]] — the same audit found that
`birationalOver_affineLine_of_not_injective_aj` is a corollary of
`birationalOver_affineLine_of_relPicEquiv_sectionIdeal`, blocked only by
declaration order.
