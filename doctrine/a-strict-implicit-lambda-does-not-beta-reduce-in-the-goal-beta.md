## A STRICT-IMPLICIT LAMBDA DOES NOT BETA-REDUCE IN THE GOAL — `beta_reduce` before `rw`

(2026-07-31, `flt-lean-17`, in `X0.lean`.) Natural families in this development are typed
`∀ {T : Scheme.{0}} (g : T ⟶ SpecQ), RelPoint f g → RelPoint jf g` — `RelPoint.pre`/`post`,
every `c` in the Hecke cluster, `IsHeckeAlbaneseRecipe`, `IsJacobianOf.aj`. When you
discharge such an existential with `refine ⟨fun {T} g x => …, …⟩`, the remaining goals
contain the **unreduced application** `(fun {T} g x => …) g' y`, because the strict-implicit
binder blocks the beta step `instantiateMVars` would otherwise do. Every `rw` then fails with

    Tactic `rewrite` failed: Did not find an occurrence of the pattern …
    in the target expression
      (fun {T} g x => …) g' (RelPoint.pre p hg x) = …

which reads as "my lemma is wrong" and is nothing of the sort. `beta_reduce` as the first
tactic of each branch fixes it; `show` with the reduced form also works but makes you write
out proof terms like `Category.comp_id g'` that the binder produced for you.

Worth its own section only because of where it bites: `X0.lean` is ~80 000 lines and one
elaboration is ~25 minutes, so discovering this against the real file costs a cycle per
branch of the `refine`. **Prototype the glue in a scratch module importing
`Fermat.FLT.Modularity.AbelianScheme` alone** — that import is 4 SECONDS, `RelPoint` and
`AbelianSchemeStruct` both live there, and `RelPoint.post` / `AbelianSchemeStruct.pre_neg`
are eight lines to re-declare locally. The whole base-point-normalisation glue for
`exists_heckeCorrespondenceFamily` was written and debugged in four such 4-second rounds and
then compiled first time in the real file. Mock the SHAPE, not just the content: a
`letI := ab.addCommGroup g` binder in front of a `Finset.sum` behaves differently from a bare
equation, and the mock is what showed the branch needs a trailing `rfl`.

