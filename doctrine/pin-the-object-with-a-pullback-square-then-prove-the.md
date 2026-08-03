## PIN THE OBJECT WITH A PULLBACK SQUARE, THEN *PROVE* THE FAITHFULNESS AUDIT — three short theorems

(2026-08-01, same module.) A leaf of the shape *"∃ a model `fZ` of `f` with properties `P`"*
is the commonest shape in this development, and its faithfulness audit is almost always
PROSE: "not vacuous because …", "hypothesis `hp` is load-bearing because …". Those two
claims are each ONE SHORT THEOREM when the leaf pins the model by an explicit `IsPullback`
square, and writing them turns an assertion a reviewer must re-derive into something the
kernel has checked.

The three, in the order they pay off:

1. **The degenerate witness is REFUTED.** The junk model is always `XZ := <the base>`,
   `fZ := 𝟙`, which satisfies every non-cartesian clause for every `X`. With the square,
   `IsPullback.isIso_snd_of_isIso` says in ONE LINE that a cartesian square over `fZ = 𝟙`
   forces `f` to be an isomorphism — so the junk witness only works for the junk `X`, and
   the leaf is not vacuous.
2. **The hypotheses are EXACTLY NECESSARY.** Every property this development asks a model
   to have (`IsProper`, `Smooth`, `Flat`, `LocallyOfFinitePresentation`, `Etale`) is
   `MorphismProperty.IsStableUnderBaseChange`, so
   `IsStableUnderBaseChange.of_isPullback sq hP` carries it back down the square to `f`.
   That is the CONVERSE of the leaf, it is two lines, and it proves — rather than asserts —
   that no hypothesis can be dropped.
3. **The conclusion is INHABITED.** Exhibit the whole chain at the trivial object
   (`X = <the base>`, `f = 𝟙`); `IsPullback.of_id_snd : IsPullback f (𝟙 _) (𝟙 _) f` is the
   square, and `IsProper (𝟙 _)` / `Smooth (𝟙 _)` are instances. This is what rules out the
   opposite failure — a leaf so over-constrained that it is a disguised contradiction, which
   no amount of "is it vacuous" checking can see.

Together (1) and (3) bracket the leaf from both sides, and (2) settles the binder list.
Total cost here: 3 theorems, 12 lines, all first-try.

**The corollary about how to STATE such a leaf: make the base change CANONICAL wherever you
can.** Where a second model has to appear — "the properties hold after enlarging the base" —
do not quantify over a new scheme and a new square. Say
`IsProper (pullback.snd fZ (specSubringMap hNM))`: the base change is the mathlib pullback,
so there is nothing to satisfy junk-wise, the compatibility with `fZ` is definitional, and
combining two such stages is one reusable PROVEN lemma (`XZ ×_R T ⟶ XZ ×_R S` is cartesian
over `Spec T ⟶ Spec S`) rather than a pile of transports. Proof irrelevance then does the
last piece of work for free: two different derivations of `zinvSubring N ≤ zinvSubring M`
are definitionally equal, so the two stages' models are literally the same term.

