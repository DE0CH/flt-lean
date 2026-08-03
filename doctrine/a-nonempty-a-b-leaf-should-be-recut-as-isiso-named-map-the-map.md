## A `Nonempty (A ≅ B)` LEAF SHOULD BE RECUT AS `IsIso <named map>` — the map is usually FORMAL, and it is what every route needs first

(2026-07-31, `RelativePicard.lean`, `nonempty_modPullback_sectionIdeal_of_isPullback`.)
A leaf whose conclusion is `Nonempty (A ≅ B)` names no morphism, so a prover has to invent
one before any mathematics can start — and every route invents the SAME one. Build it, prove
it exists, and leave `IsIso` of it as the leaf. The trade is one leaf for one leaf, and what
changes is that the residual is a statement about a *named term* instead of an existential
that a prover could satisfy by an unrelated isomorphism.

**The construction is usually adjunction bookkeeping and nothing else.** Here `A = φ^*ker η_σ`
and `B = ker η_{σ'}`; the map is `φ^*(kernel.ι) ≫ (unit iso)` lifted through `kernel.lift`, and
the side condition is discharged by transposing across `σ'^* ⊣ σ'_*`:

* `F.map (kernel.ι η) = 0` where `η = adj.unit.app X` — because `F.map η` is a **SPLIT MONO**
  (`Adjunction.left_triangle_components` is literally its retraction), so
  `F.map (kernel.ι η) ≫ F.map η = F.map (kernel.ι η ≫ η) = F.map 0 = 0` cancels. This uses
  nothing whatever about the morphism `σ` and is four lines;
* transport that across a commuting square with `Scheme.Modules.pullbackComp` /
  `pullbackCongr` plus a three-line `map_eq_zero_of_natIso` (`F ≅ G`, `G.map u = 0` ⟹
  `F.map u = 0`);
* then `u ≫ adj.unit.app N = 0` follows from `F.map u = 0` by UNIT NATURALITY —
  `u ≫ unit.app N = unit.app M ≫ (F ⋙ G).map u` — not by a `homEquiv` computation.

Both `Scheme.Modules.pullback f` and `pushforward f` are registered `Additive` at this pin, so
`Functor.map_zero` is free; do not go looking for a `PreservesZeroMorphisms` instance to build.

**Say in the commit that the count did not move**, and say what got smaller instead. A
`−1 +1` warning-set delta is indistinguishable from "nothing happened" to every scan.

### THE `(𝟭 C).obj X` WRAPPER ON ADJUNCTION COMPONENTS BREAKS `rw`, AND THE ERROR PRINTS TWO IDENTICAL TYPES

Three round trips went to this and it will bite anyone touching `Adjunction.unit`/`counit`.
`adj.unit.app X : (𝟭 C).obj X ⟶ (F ⋙ G).obj X`, so every object downstream of it carries a
`(𝟭 _).obj` wrapper that is `rfl`-equal to the bare object and **not** syntactically equal.
Consequences, each observed:

* `have htri : … = 𝟙 _ := adj.left_triangle_components _` elaborates the `_` from the LHS and
  produces `𝟙 (F.obj ((𝟭 C).obj X))`, where the surrounding term wants
  `𝟙 ((𝟭 D).obj (F.obj X))`. `rw [htri] at key` then makes `key` ill-typed at `instances`
  transparency and the NEXT rewrite fails with a message about the wrong lemma;
* `simpa using key` fails reporting **`term key has type <T> but is expected to have type <T>`**
  with the two `<T>` printed character-for-character identically;
* `rw [comp_zero]` fails with `Did not find an occurrence of the pattern ?m ≫ 0` on a goal that
  visibly displays `f ≫ 0 = 0`, leaving `⊢ 0 = 0` that `rfl` does not close.

The cures, in order of preference: **do not create the `≫ 𝟙` in the first place** — get
`f = 0` from `f ≫ g = 0` with `g` a split mono via `Limits.zero_of_comp_mono` and
`IsSplitMono` built directly from the triangle identity, rather than by cancelling an
identity; and **use a defeq-checking tactic where `rw` fails** — `exact comp_zero` closes what
`rw [comp_zero]` cannot, and `refine h.trans ?_` crosses the `(𝟭 _).map u` vs `u` gap that
`rw [h]` cannot. This is the same family as the standing "printed pattern equals printed
target ⟹ switch to `exact`/`Eq.trans`" rule, with a new and very common cause.

### `lake env lean` ON A 6000-LINE MODULE EXCEEDS THE 10-MINUTE FOREGROUND LIMIT

`RelativePicard.lean` was ~4400 lines when the task prompt was written ("~25 s with
`lake env lean`, so develop against the real file") and is 6100 now; one elaboration is well
over ten minutes and a foreground Bash call dies with exit 143, which reads like a kill.
**Re-measure a prompt's stated iteration cost before believing it** — these files grow by
thousands of lines per release. The scratch-module route was ~100 s per round here (one
`public import` of the target's own built olean, restating the new declarations under
throwaway names), i.e. a 6× round-trip win, and the text moved into the real file compiled
first try.

