## A ROUTE THAT SAYS "TAKE STALKS" IS DISCHARGED BY THE ADJUNCTION THAT *DEFINES* THE OBJECT
(2026-08-02, `flt-lean-72`, closing `exists_constSmul_of_iso` — the last leaf of
`RelativePicard.lean`'s `𝒦_X` dictionary.) That leaf's docstring gave a four-bullet route,
and the fourth bullet was the expensive-looking one: *"the identity of MORPHISMS follows
from the identity on the generic stalk, because `Γ(𝒦_X, U) ⟶ (𝒦_X)_η` is injective for
every `U` … this is the one step that uses what `𝒦_X` IS"*, with the file's own
`injective_genericPointHom_app` named as the ingredient. The first three bullets were
stalk-theoretic too — exactness of stalk-taking, `Mono` as objectwise injectivity, a
`K`-submodule dichotomy.
**None of it was needed, and the reason is one line of the object's own definition.**
`constSheaf X` is `g_* 𝒪_{Spec K}` BY DEFINITION (`g` = the generic point as a morphism),
so `Hom(L, 𝒦_X) ≅ Hom(g^*L, 𝒪_{Spec K})` is just the `g^* ⊣ g_*` adjunction — and being a
**bijection** it discharges bullet four outright: two morphisms into `𝒦_X` are equal iff
their transposes are. No stalk, no colimit, no exactness, and `injective_genericPointHom_app`
never appears. The whole argument then lives in `(Spec K).Modules`, where the only inputs
are local triviality at `η` and "every endomorphism of `𝒪` is multiplication by a global
section".
**The generalisable check, and it costs one `grep` of the definition:** when a route note
says a step needs STALKS, LOCAL-TO-GLOBAL, or "determined by its germ", look at how the
object is DEFINED. If it is a pushforward, a kernel of an adjunction unit, or anything else
presented by an adjunction, that adjunction's `homEquiv` is a bijection and it is very often
the step the note was pricing. This development defines objects that way constantly —
`sectionIdeal` is a kernel of an adjunction unit, `constSheaf` is a pushforward — and the
file's own `toConstSheaf_eq`/`mono_toConstSheaf` had already used the trick at one point
without anybody noticing it applies to the dictionary too.
Two riders from the same run, both cheap and both reusable.
* **A LOCAL-TRIVIALITY definition beats an abstract-invertibility one when you need a
  trivialization AT A POINT.** `IsInvertibleSheaf L` here is `∀ z, ∃ U ∋ z, L|_U ≅ 𝒪_U`, so
  `g^*L ≅ 𝒪_{Spec K}` is: take `U` at `η`, factor `g` through `U` with
  `IsOpenImmersion.lift` (its range condition IS `preimage_genericPointHom_eq_top`), then
  four pseudo-functoriality isos the file already has. **Do NOT go the other way** — via
  `isInvertibleSheaf_modPullback` and "the only nonempty open of `Spec K` is `⊤`" — which
  buys the same iso and adds restriction-along-`⊤` bookkeeping this route never meets.
* **`Adjunction.homEquiv_naturality_left_symm` / `_right_symm` are the two lemmas that turn
  the transposed goal back into the original**, and they are exactly the right shape; the
  only care needed is to apply them as `have`s and chain with `Eq.trans`, because the goal's
  type is the project's `def` (`constSheaf X`) and `rw` will not cross that (next section).
