## `LinearMap`'s coercion does not fire inside a `Subgroup` structure instance — `AddMonoidHom`'s does

(2026-07-31, flt-lean-290.) With `letI : Module (ZMod p) M := AddCommGroup.zmodModule …` in scope
and `f : M →ₗ[ZMod p] ZMod p` in context, `f x` elaborates fine in an ordinary `have` and fails
inside

    set NB : Subgroup G := { carrier := {h | h ∈ N₁ ∧ f (e h) = 0}, one_mem' := …, … }

with `Function expected at f, but this term has type M →ₗ[ZMod p] ZMod p` — i.e. the `FunLike`
instance is not found, because it wants the `Module` instance and instance search does not reach a
local `letI` from inside a structure-instance field. The one-line fix is to carry the map as an
`AddMonoidHom` (`LinearMap.toAddMonoidHom`), whose `FunLike` needs no module structure; `map_add`,
`map_zero` and `map_neg` all still apply, so no proof changes. Do the conversion at the `obtain`,
not at the use site.

